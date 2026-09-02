//! Derivation of an SMT-LIB logic (and the solver options it implies) from the
//! actual contents of a query.
//!
//! Verus otherwise tells cvc5 `(set-logic ALL)`, which cvc5 warns about:
//! "Consider setting a stricter logic for (likely) better performance." A
//! stricter logic also *unlocks* options that are unsound or unsupported in the
//! general case -- most importantly eager bit-blasting, which is only available
//! for quantifier-free bit-vector problems and which is dramatically faster on
//! them.
//!
//! IMPORTANT: a derived logic can only be applied to a context whose full
//! content is known before anything is sent to the solver, because cvc5 locks
//! its configuration at the first `assert` ("solver is already fully
//! initialized"). In practice that means single-query, prelude-free contexts
//! (`by(bit_vector)`); an incremental context accumulates queries after the
//! prelude has already been sent and must stay on the conservative logic.

use crate::ast::{
    BindX, Constant, Decl, DeclX, Expr, ExprX, MultiOp, Query, Stmt, StmtX, Typ, TypX,
};
use crate::context::SmtSolver;

/// Which theories a query actually touches.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LogicFeatures {
    pub quantifiers: bool,
    pub bitvec: bool,
    pub uninterp: bool,
    pub datatypes: bool,
    pub ints: bool,
    pub reals: bool,
    pub nonlinear: bool,
    /// Something we deliberately do not model (floats, Z3 special relations,
    /// higher-order application, ...). Forces the conservative logic.
    pub unmodeled: bool,
}

/// A derived logic plus the options it makes available.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogicSpec {
    /// e.g. "QF_UFBV". `None` means "do not narrow the logic".
    pub logic: Option<String>,
    /// `(set-option :k v)` pairs to emit alongside the logic.
    pub options: Vec<(String, String)>,
}

impl LogicSpec {
    pub fn conservative() -> Self {
        LogicSpec { logic: None, options: vec![] }
    }
}

impl LogicFeatures {
    /// Compose an SMT-LIB logic name, in the conventional order
    /// `[QF_][A]UF[DT][BV][N|L][I][R]A`.
    ///
    /// Only names validated against the solver are returned; anything else
    /// yields `None` so the caller keeps the conservative logic. Composing
    /// logic names is not free-form -- an unrecognized string is a hard error
    /// (`cvc5: (error ...)`), so guessing is worse than not narrowing.
    fn logic_name(&self) -> Option<String> {
        if self.unmodeled {
            return None;
        }
        let mut s = String::new();
        if !self.quantifiers {
            s.push_str("QF_");
        }
        // AIR always emits `(declare-sort %%Function%% 0)` in ensure_started,
        // so UF is present in every query regardless of what else appears.
        s.push_str("UF");
        if self.datatypes {
            s.push_str("DT");
        }
        if self.bitvec {
            s.push_str("BV");
        }
        match (self.ints, self.reals) {
            (false, false) => {}
            (i, r) => {
                s.push(if self.nonlinear { 'N' } else { 'L' });
                if i {
                    s.push('I');
                }
                if r {
                    s.push('R');
                }
                s.push('A');
            }
        }
        // Allowlist: only shapes confirmed accepted by the solvers we drive.
        const KNOWN: &[&str] = &["QF_UFBV", "UFBV"];
        if KNOWN.contains(&s.as_str()) { Some(s) } else { None }
    }

    /// Options unlocked by these features, for this solver.
    fn options(&self, solver: &SmtSolver) -> Vec<(String, String)> {
        let mut opts = vec![];
        match solver {
            SmtSolver::Cvc5 => {
                // Eager bit-blasting is markedly faster on quantifier-free
                // bit-vector goals (measured: one Verus query went from an
                // unsolved 120s to 0.02s). It is rejected outright for
                // quantified logics ("ackermann not supported in quantified
                // logics") and conflicts with model generation, so it is only
                // safe when the goal is quantifier-free.
                if self.bitvec && !self.quantifiers && !self.unmodeled {
                    opts.push(("bitblast".to_string(), "eager".to_string()));
                    // Eager bit-blasting cannot produce models for BV+UF. This
                    // is sound here only because such queries run as a single
                    // check-sat with no model-based error localization: see
                    // `single_check_query` in smt_verify.rs, which reports at
                    // the query level and never asks for a model.
                    opts.push(("produce-models".to_string(), "false".to_string()));
                }
            }
            SmtSolver::Z3 => {}
        }
        opts
    }

    pub fn to_spec(&self, solver: &SmtSolver) -> LogicSpec {
        match self.logic_name() {
            None => LogicSpec::conservative(),
            Some(logic) => LogicSpec { logic: Some(logic), options: self.options(solver) },
        }
    }
}

/// Collect the features of `query`, together with any global `decls` that will
/// be in scope for it.
pub fn features_of(decls: &[Decl], query: &Query) -> LogicFeatures {
    let mut f = LogicFeatures::default();
    // AIR always declares the %%Function%% sort (context.rs, ensure_started).
    f.uninterp = true;
    for d in decls {
        decl(&mut f, d);
    }
    for d in query.local.iter() {
        decl(&mut f, d);
    }
    stmt(&mut f, &query.assertion);
    f
}

fn decl(f: &mut LogicFeatures, d: &Decl) {
    match &**d {
        DeclX::Sort(_) => f.uninterp = true,
        DeclX::Datatypes(dts) => {
            f.datatypes = true;
            for dt in dts.iter() {
                for variant in dt.a.iter() {
                    for field in variant.a.iter() {
                        typ(f, &field.a);
                    }
                }
            }
        }
        DeclX::Const(_, t) | DeclX::Var(_, t) => typ(f, t),
        DeclX::Fun(_, args, ret) => {
            f.uninterp = true;
            for a in args.iter() {
                typ(f, a);
            }
            typ(f, ret);
        }
        DeclX::Axiom(ax) => expr(f, &ax.expr),
    }
}

fn typ(f: &mut LogicFeatures, t: &Typ) {
    match &**t {
        TypX::Bool => {}
        TypX::Int => f.ints = true,
        TypX::Real => f.reals = true,
        TypX::BitVec(_) => f.bitvec = true,
        TypX::Named(_) => f.uninterp = true,
        // A TypX::Fun is encoded as the uninterpreted %%Function%% sort, not as
        // an SMT array, so it contributes UF rather than the array theory.
        TypX::Fun => f.uninterp = true,
        // Floats would need FP in the logic name; not modeled.
        TypX::Float { .. } => f.unmodeled = true,
    }
}

fn stmt(f: &mut LogicFeatures, s: &Stmt) {
    match &**s {
        StmtX::Assume(e) => expr(f, e),
        StmtX::Assert(_, _, _, e) => expr(f, e),
        StmtX::Assign(_, e) => expr(f, e),
        StmtX::Havoc(_) | StmtX::Snapshot(_) | StmtX::Break(_) => {}
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => stmt(f, s),
        StmtX::Block(ss) | StmtX::Switch(ss) => {
            for s in ss.iter() {
                stmt(f, s);
            }
        }
    }
}

/// True if `e` is a literal, for distinguishing linear from nonlinear products.
fn is_const(e: &Expr) -> bool {
    matches!(&**e, ExprX::Const(_))
}

fn expr(f: &mut LogicFeatures, e: &Expr) {
    use crate::ast::{BinaryOp as B, UnaryOp as U};
    match &**e {
        ExprX::Const(c) => match c {
            Constant::Bool(_) => {}
            Constant::Nat(_) => f.ints = true,
            Constant::Real(_) => f.reals = true,
            Constant::BitVec(_, _) => f.bitvec = true,
        },
        ExprX::Var(_) | ExprX::Old(_, _) => {}
        ExprX::Apply(_, args) => {
            f.uninterp = true;
            for a in args.iter() {
                expr(f, a);
            }
        }
        // Higher-order application has no plain first-order logic name.
        ExprX::ApplyFun(_, _, _) => f.unmodeled = true,
        ExprX::Unary(op, e1) => {
            match op {
                U::Not => {}
                U::BitNot
                | U::BitNeg
                | U::BitExtract(..)
                | U::BitZeroExtend(_)
                | U::BitSignExtend(_) => f.bitvec = true,
                U::ToReal | U::FloatToReal | U::RealToInt => f.reals = true,
                _ => f.unmodeled = true, // float predicates/conversions
            }
            expr(f, e1);
        }
        ExprX::Binary(op, e1, e2) => {
            match op {
                B::Implies | B::Eq => {}
                B::Le | B::Ge | B::Lt | B::Gt => {}
                B::EuclideanDiv | B::EuclideanMod => {
                    f.ints = true;
                    // Division by a non-literal is nonlinear.
                    if !is_const(e2) {
                        f.nonlinear = true;
                    }
                }
                B::RealDiv => {
                    f.reals = true;
                    if !is_const(e2) {
                        f.nonlinear = true;
                    }
                }
                B::BitXor
                | B::BitAnd
                | B::BitOr
                | B::BitAdd
                | B::BitSub
                | B::BitMul
                | B::BitUDiv
                | B::BitURem
                | B::BitSDiv
                | B::BitSRem
                | B::BitULt
                | B::BitUGt
                | B::BitULe
                | B::BitUGe
                | B::BitSLt
                | B::BitSGt
                | B::BitSLe
                | B::BitSGe
                | B::AShr
                | B::LShr
                | B::Shl
                | B::BitConcat => f.bitvec = true,
                // Z3 special relations and float comparisons have no logic name.
                _ => f.unmodeled = true,
            }
            expr(f, e1);
            expr(f, e2);
        }
        ExprX::Multi(op, es) => {
            match op {
                MultiOp::And | MultiOp::Or | MultiOp::Xor | MultiOp::Distinct => {}
                MultiOp::Add | MultiOp::Sub => f.ints = true,
                MultiOp::Mul => {
                    f.ints = true;
                    // A product of two or more non-literals is nonlinear.
                    if es.iter().filter(|e| !is_const(e)).count() >= 2 {
                        f.nonlinear = true;
                    }
                }
                MultiOp::Float => f.unmodeled = true,
            }
            for e in es.iter() {
                expr(f, e);
            }
        }
        ExprX::IfElse(a, b, c) => {
            expr(f, a);
            expr(f, b);
            expr(f, c);
        }
        // `array` builds a %%Function%% value; uninterpreted, not SMT arrays.
        ExprX::Array(es) => {
            f.uninterp = true;
            for e in es.iter() {
                expr(f, e);
            }
        }
        ExprX::Bind(b, body) => {
            match &**b {
                BindX::Let(bs) => {
                    for bnd in bs.iter() {
                        expr(f, &bnd.a);
                    }
                }
                BindX::Quant(_, bs, trigs, _) => {
                    f.quantifiers = true;
                    for bnd in bs.iter() {
                        typ(f, &bnd.a);
                    }
                    for t in trigs.iter() {
                        for e in t.iter() {
                            expr(f, e);
                        }
                    }
                }
                // Lambda and choose both introduce binders that AIR lowers via
                // the %%Function%% sort and quantified axioms.
                BindX::Lambda(..) | BindX::Choose(..) => {
                    f.quantifiers = true;
                    f.uninterp = true;
                }
            }
            expr(f, body);
        }
        ExprX::LabeledAxiom(_, _, e) | ExprX::LabeledAssertion(_, _, _, e) => expr(f, e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::CommandX;
    use sise::TreeNode as Node;

    /// Parse AIR source text and return its single `check-valid` query.
    /// These tests never launch a solver -- derivation is a pure function.
    fn query_of(text: &str) -> Query {
        let wrapped = format!("({})", text);
        let mut p = sise::Parser::new(&wrapped);
        let node = sise::parse_tree(&mut p).expect("parse");
        let nodes = match node {
            Node::List(nodes) => nodes,
            Node::Atom(_) => panic!("expected a list"),
        };
        let mi = std::sync::Arc::new(crate::messages::AirMessageInterface {});
        let commands =
            crate::parser::Parser::new(mi).nodes_to_commands(&nodes).expect("nodes_to_commands");
        for c in commands.iter() {
            if let CommandX::CheckValid(q) = &**c {
                return q.clone();
            }
        }
        panic!("no check-valid in fixture");
    }

    fn features(text: &str) -> LogicFeatures {
        features_of(&[], &query_of(text))
    }

    fn cvc5_spec(text: &str) -> LogicSpec {
        features(text).to_spec(&SmtSolver::Cvc5)
    }

    fn has_opt(spec: &LogicSpec, k: &str, v: &str) -> bool {
        spec.options.iter().any(|(a, b)| a == k && b == v)
    }

    // ---- feature detection -------------------------------------------------

    #[test]
    fn detects_bitvec_from_sort() {
        let f = features("(check-valid (declare-const x (_ BitVec 32)) (assert (= x x)))");
        assert!(f.bitvec);
        assert!(!f.quantifiers);
        assert!(!f.ints);
        // AIR always declares the %%Function%% sort, so UF is always present.
        assert!(f.uninterp);
    }

    #[test]
    fn detects_quantifier() {
        let f = features(
            "(check-valid (declare-const x (_ BitVec 32))
                          (assert (forall ((y (_ BitVec 32))) (= y y))))",
        );
        assert!(f.bitvec);
        assert!(f.quantifiers);
    }

    #[test]
    fn detects_ints_but_not_bitvec() {
        let f = features("(check-valid (declare-const n Int) (assert (= n n)))");
        assert!(f.ints);
        assert!(!f.bitvec);
    }

    #[test]
    fn product_of_two_variables_is_nonlinear() {
        let f = features(
            "(check-valid (declare-const a Int) (declare-const b Int)
                          (assert (= (* a b) (* b a))))",
        );
        assert!(f.nonlinear, "a*b must count as nonlinear");
    }

    #[test]
    fn product_with_one_literal_is_linear() {
        let f = features("(check-valid (declare-const a Int) (assert (= (* 2 a) (* a 2))))");
        assert!(!f.nonlinear, "2*a must stay linear");
    }

    // ---- logic naming ------------------------------------------------------

    #[test]
    fn quantifier_free_bitvec_yields_qf_ufbv() {
        let spec = cvc5_spec("(check-valid (declare-const x (_ BitVec 32)) (assert (= x x)))");
        assert_eq!(spec.logic.as_deref(), Some("QF_UFBV"));
    }

    #[test]
    fn quantified_bitvec_yields_ufbv() {
        let spec = cvc5_spec(
            "(check-valid (declare-const x (_ BitVec 32))
                          (assert (forall ((y (_ BitVec 32))) (= y y))))",
        );
        assert_eq!(spec.logic.as_deref(), Some("UFBV"));
    }

    #[test]
    fn shapes_outside_the_allowlist_stay_conservative() {
        // Integer arithmetic composes to QF_UFLIA, which is not on the
        // allowlist, so no logic is emitted rather than an unverified guess.
        let spec = cvc5_spec("(check-valid (declare-const n Int) (assert (= n n)))");
        assert_eq!(spec.logic, None);
        assert!(spec.options.is_empty());
    }

    // ---- implied options ---------------------------------------------------

    #[test]
    fn eager_bitblast_only_when_quantifier_free() {
        let qf = cvc5_spec("(check-valid (declare-const x (_ BitVec 32)) (assert (= x x)))");
        assert!(has_opt(&qf, "bitblast", "eager"));
        // Eager bit-blasting cannot produce models for BV+UF, so models must be
        // disabled alongside it.
        assert!(has_opt(&qf, "produce-models", "false"));

        // cvc5 rejects eager bit-blasting outright in a quantified logic
        // ("ackermann not supported in quantified logics").
        let quantified = cvc5_spec(
            "(check-valid (declare-const x (_ BitVec 32))
                          (assert (forall ((y (_ BitVec 32))) (= y y))))",
        );
        assert!(!has_opt(&quantified, "bitblast", "eager"));
        assert!(!has_opt(&quantified, "produce-models", "false"));
    }

    #[test]
    fn z3_gets_no_implied_options() {
        let spec = features("(check-valid (declare-const x (_ BitVec 32)) (assert (= x x)))")
            .to_spec(&SmtSolver::Z3);
        assert!(spec.options.is_empty(), "these options are cvc5-specific");
    }

    #[test]
    fn unmodeled_features_force_the_conservative_logic() {
        let mut f = LogicFeatures::default();
        f.bitvec = true;
        f.uninterp = true;
        f.unmodeled = true;
        let spec = f.to_spec(&SmtSolver::Cvc5);
        assert_eq!(spec.logic, None);
        assert!(spec.options.is_empty(), "no options without a narrowed logic");
    }
}
