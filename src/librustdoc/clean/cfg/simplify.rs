use std::fmt::Display;
use std::str::FromStr;

use egg::{AstSize, Extractor, Id, RecExpr, Rewrite, Runner, define_language, rewrite};
use rustc_data_structures::fx::FxHashMap;
use rustc_span::Symbol;
use tracing::{debug, instrument};

use super::Cfg;

pub(crate) struct SimplifyCfgCache {
    // FIXME: somehow cache egraph to avoid redundant intermediate calculations?
    rules: Vec<Rewrite<CfgLang, ()>>,
    memo: FxHashMap<Cfg, Cfg>,
}

impl Default for SimplifyCfgCache {
    fn default() -> Self {
        Self { rules: make_rules(), memo: Default::default() }
    }
}

#[instrument(level = "debug", skip(cache), ret)]
pub(crate) fn simplify_cfg(cfg: Cfg, cache: &mut SimplifyCfgCache) -> Cfg {
    if cache.memo.contains_key(&cfg) {
        return cache.memo[&cfg].clone();
    }
    let raw_expr = cfg_to_expr(&cfg);
    let expr = perform_simplify(raw_expr, cache);
    let new_cfg = expr_to_cfg(&expr);
    cache.memo.insert(cfg, new_cfg.clone());
    new_cfg
}

#[instrument(level = "debug", skip(cache), ret)]
fn perform_simplify(expr: RecExpr<CfgLang>, cache: &mut SimplifyCfgCache) -> RecExpr<CfgLang> {
    let egraph = Default::default();
    let mut runner = Runner::default().with_egraph(egraph);
    let root = runner.egraph.add_expr(&expr);
    let runner = runner.run(&cache.rules);

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    debug!("cost {best_cost}");
    best
}

#[instrument(level = "debug", ret)]
fn cfg_to_expr(cfg: &Cfg) -> RecExpr<CfgLang> {
    fn convert_multi(
        children: &[Cfg],
        expr: &mut RecExpr<CfgLang>,
        op: fn([Id; 2]) -> CfgLang,
    ) -> Option<Id> {
        let mut children = children.iter();
        let first = children.next()?;
        let mut left = convert_into(first, expr);
        for next_cfg in children {
            let next = convert_into(next_cfg, expr);
            left = expr.add(op([left, next]));
        }
        Some(left)
    }

    fn convert_into(cfg: &Cfg, expr: &mut RecExpr<CfgLang>) -> Id {
        match cfg {
            Cfg::True => expr.add(CfgLang::True),
            Cfg::False => expr.add(CfgLang::False),
            &Cfg::Cfg(key, val) => expr.add(CfgLang::Term(CfgTerm { key, val })),
            Cfg::Not(child) => {
                let id = convert_into(&*child, expr);
                expr.add(CfgLang::Not(id))
            }
            Cfg::Any(children) => convert_multi(children, expr, CfgLang::Or)
                .unwrap_or_else(|| convert_into(&Cfg::False, expr)),
            Cfg::All(children) => convert_multi(children, expr, CfgLang::And)
                .unwrap_or_else(|| convert_into(&Cfg::True, expr)),
        }
    }

    let mut expr = RecExpr::default();
    convert_into(cfg, &mut expr);
    expr
}

#[instrument(level = "debug", ret)]
fn expr_to_cfg(expr: &RecExpr<CfgLang>) -> Cfg {
    fn expr_to_cfg_rec(expr: &RecExpr<CfgLang>, id: Id) -> Cfg {
        let root = &expr[id];
        match *root {
            CfgLang::True => Cfg::True,
            CfgLang::False => Cfg::False,
            CfgLang::Term(CfgTerm { key, val }) => Cfg::Cfg(key, val),
            CfgLang::Not(id) => Cfg::Not(Box::new(expr_to_cfg_rec(expr, id))),
            // FIXME: collapse nested ORs/ANDs
            CfgLang::Or([left, right]) => {
                Cfg::Any(vec![expr_to_cfg_rec(expr, left), expr_to_cfg_rec(expr, right)])
            }
            CfgLang::And([left, right]) => {
                Cfg::All(vec![expr_to_cfg_rec(expr, left), expr_to_cfg_rec(expr, right)])
            }
        }
    }

    expr_to_cfg_rec(expr, Id::from(expr.len() - 1))
}

define_language! {
    enum CfgLang {
        "true" = True,
        "false" = False,
        Term(CfgTerm),
        "not" = Not(Id),
        "or" = Or([Id; 2]),
        "and" = And([Id; 2]),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CfgTerm {
    pub key: Symbol,
    pub val: Option<Symbol>,
}

impl Display for CfgTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let key = self.key;
        match self.val {
            None => write!(f, "{key}"),
            // FIXME: handle escaping vals with spaces or unusual chars
            Some(val) => write!(f, "{key}={val}"),
        }
    }
}

impl FromStr for CfgTerm {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty() {
            return Err("empty");
        }

        // FIXME: handle escaping vals with spaces or unusual chars
        match s.split_once(&['=']) {
            Some((key, val)) => {
                // Note that in practice this function should only be called when parsing
                // rewrite rules, so the symbol interning should be cheap.
                Ok(Self { key: Symbol::intern(key), val: Some(Symbol::intern(val)) })
            }
            _ => Ok(Self { key: Symbol::intern(s), val: None }),
        }
    }
}

fn make_rules() -> Vec<Rewrite<CfgLang, ()>> {
    let oneway = [
        rewrite!("commute-or"; "(or ?a ?b)" => "(or ?b ?a)"),
        rewrite!("commute-and"; "(and ?a ?b)" => "(and ?b ?a)"),
        rewrite!("annihil-or"; "(or ?a true)" => "true"),
        rewrite!("annihil-and"; "(and ?a false)" => "false"),
        rewrite!("absorp1"; "(and ?a (or ?a ?b))" => "?a"),
        rewrite!("absorp2"; "(or ?a (and ?a ?b))" => "?a"),
        rewrite!("lem-or"; "(or ?a (not ?a))" => "true"),
        rewrite!("lem-and"; "(and ?a (not ?a))" => "false"),
    ];
    let bidi = [
        rewrite!("assoc-or"; "(or ?a (or ?b ?c))" <=> "(or (or ?a ?b) ?c)"),
        rewrite!("assoc-and"; "(and ?a (and ?b ?c))" <=> "(and (and ?a ?b) ?c)"),
        rewrite!("distrib-and-over-or"; "(and ?a (or ?b ?c))" <=> "(or (and ?a ?b) (and ?a ?c))"),
        rewrite!("distrib-or-over-and"; "(or ?a (and ?b ?c))" <=> "(and (or ?a ?b) (or ?a ?c))"),
        rewrite!("ident-or"; "(or ?a false)" <=> "?a"),
        rewrite!("ident-and"; "(and ?a true)" <=> "?a"),
        rewrite!("idemp-or"; "(or ?a ?a)" <=> "?a"),
        rewrite!("idemp-and"; "(and ?a ?a)" <=> "?a"),
        rewrite!("demorgan-or"; "(not (or ?a ?b))" <=> "(and (not ?a) (not ?b))"),
        rewrite!("demorgan-and"; "(not (and ?a ?b))" <=> "(or (not ?a) (not ?b))"),
    ];
    oneway.into_iter().chain(bidi.into_iter().flatten()).collect()
}
