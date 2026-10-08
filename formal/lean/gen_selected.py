#!/usr/bin/env python3
"""Generates `KappaCheck/Selected.lean`: main's selected witness κ = 25508460085039/5·10¹⁷.

Inputs (repository root):
  research/matrix-exponent-synthesis/candidate/arithmetic.json   bit network, a_b, κ, h, assembly
  certificates/copied-centers-network.json                        complex network, a_c = 717/10⁷

The Lean file states the moments as real-number inequalities and the 47 slacks as formulas
transcribed from `research/copied-fixed-reversed/balanced_assembly.py`. Every number this script
computes (logarithm enclosures, rounded exponential bounds) is only a proof hint: Lean rechecks it.
The certificate values the Lean literals restate are compared to the JSON by `Selected.lean`'s own
theorems (`slack_values`, `margin_values`, `semantic_values`) and by `sources.py`.

`python3 formal/lean/gen_selected.py` writes the file; `--check` fails if it is stale.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent/'KappaCheck'/'Selected.lean'
ARITH = 'research/matrix-exponent-synthesis/candidate/arithmetic.json'
CXNET = 'certificates/copied-centers-network.json'

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 37]
BASIS = [16, 25, 81, 126, 176, 351, 715, 343, 576, 481]   # log(n/(n-1)) = -log(1 - 1/n)
ROUND = 10**40                                           # rounding grid of every hint
BIT_SHIFT = Q(1, 10**16)                                 # negative controls: a + shift fails
CX_SHIFT = Q(1, 10**7)


def factor(n):
    v = []
    for p in PRIMES:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        v.append(e)
    assert n == 1
    return v


MAT = [[x-y for x, y in zip(factor(n), factor(n-1))] for n in BASIS]


def coefficients(num, den):
    """Integers c with num/den = Π (n_i/(n_i - 1))^c_i."""
    k = len(PRIMES)
    rows = [[Q(MAT[j][i]) for j in range(k)]+[Q(x-y)]
            for i, (x, y) in enumerate(zip(factor(num), factor(den)))]
    for col in range(k):
        piv = next(r for r in range(col, k) if rows[r][col])
        rows[col], rows[piv] = rows[piv], rows[col]
        rows[col] = [x/rows[col][col] for x in rows[col]]
        for r in range(k):
            if r != col and rows[r][col]:
                f = rows[r][col]
                rows[r] = [x-f*y for x, y in zip(rows[r], rows[col])]
    c = [row[k] for row in rows]
    assert all(x.denominator == 1 for x in c)
    return [int(x) for x in c]


def down(x):
    return Q(x.numerator*ROUND//x.denominator, ROUND)


def up(x):
    return -down(-x)


def terms(x):
    n = 1
    while x**(n+1)/(1-x) >= Q(1, 10**44):
        n += 1
    return n


def ps(x, n):
    return sum(x**(i+1)/(i+1) for i in range(n))


BASIS_DATA = []
for nb in BASIS:
    x = Q(1, nb)
    n = terms(x)
    err = x**(n+1)/(1-x)
    BASIS_DATA.append((nb, n, down(ps(x, n)-err), up(ps(x, n)+err)))


def log_bounds(m, t):
    c = coefficients(m, t)
    lo = sum(ci*(BASIS_DATA[i][2] if ci > 0 else BASIS_DATA[i][3]) for i, ci in enumerate(c))
    hi = sum(ci*(BASIS_DATA[i][3] if ci > 0 else BASIS_DATA[i][2]) for i, ci in enumerate(c))
    return c, lo, hi


def P4(v):
    return 1+v+v**2/2+v**3/6+5*v**4/96


def S5(v):
    return 1+v+v**2/2+v**3/6+v**4/24


def lit(x):
    x = Q(x)
    return str(x.numerator) if x.denominator == 1 else f'{x.numerator} / {x.denominator}'


def plit(x):
    x = Q(x)
    if x.denominator == 1:
        return f'({x.numerator} : ℚ)' if x >= 0 else f'(-{-x.numerator} : ℚ)'
    return f'({lit(x)} : ℚ)' if x >= 0 else f'(-({lit(-x)}) : ℚ)'


def load():
    a = json.loads((ROOT/ARITH).read_text())
    cx = json.loads((ROOT/CXNET).read_text())
    sp = a['source_profile']
    bit = dict(m=sp['m'], W=sp['W'], N=sp['N'], L=sp['L'], a=Q(a['bit_saving']),
               rows=sorted((int(t), n) for t, n in sp['child_multiplicities'].items()))
    fc = cx['finite_bridge']['complex']
    assert a['finite_bridge']['complex'] == fc
    com = dict(m=fc['m'], W=fc['W'], a=Q(cx['complex']['saving']),
               rows=[(t, n) for t, n in cx['complex']['child_width_multiplicities']])
    return a, bit, com


def network(name, net, shift):
    m, W, a, rows = net['m'], net['W'], net['a'], net['rows']
    data = []
    up_sum = Q(0)
    lo_sum = Q(0)
    for t, n in rows:
        c, lo, hi = log_bounds(m, t)
        assert 0 <= a*hi <= 1 and lo >= 0
        U = up(P4(a*hi))
        D = down(S5((a+shift)*lo))
        up_sum += Q(n*t, m)*U
        lo_sum += Q(n*t, m)*D
        data.append((t, n, c, lo, hi, U, D))
    assert up_sum < W < lo_sum, name
    return data


def match_def(name, doc, pairs):
    out = [f'/-- {doc} -/', f'def {name} : ℕ → ℚ']
    out += [f'  | {t} => {lit(v)}' for t, v in pairs]
    out.append('  | _ => 0')
    return out


def rows_def(name, doc, rows):
    body = ',\n  '.join(', '.join(f'({t}, {n})' for t, n in rows[i:i+4]) for i in range(0, len(rows), 4))
    return [f'/-- {doc} -/', f'def {name} : List (ℕ × ℕ) := [\n  {body}]']


def cases(n):
    return 'rcases hr with ' + ' | '.join(['rfl']*n)


def network_lean(tag, label, net, data, shift, aname):
    m, W = net['m'], net['W']
    R, Hlo, Hhi, U, D = (f'{tag}Rows', f'{tag}Hlo', f'{tag}Hhi', f'{tag}U', f'{tag}D')
    out = []
    out += rows_def(R, f'{label}: `(t, n_t)` for every child width `t`', [(t, n) for t, n, *_ in data])
    out += match_def(Hlo, f'{label}: lower bounds on `log(m/t)`', [(d[0], d[3]) for d in data])
    out += match_def(Hhi, f'{label}: upper bounds on `log(m/t)`', [(d[0], d[4]) for d in data])
    out += match_def(U, f'{label}: upward-rounded `P₄(a·Hhi t)`', [(d[0], d[5]) for d in data])
    out += match_def(D, f'{label}: downward-rounded `S₅((a+shift)·Hlo t)` (negative control)',
                     [(d[0], d[6]) for d in data])
    out.append('')
    # logarithms
    out.append('set_option maxHeartbeats 20000000 in')
    out.append(f'/-- {label}: `Hlo t ≤ log(m/t) ≤ Hhi t` for every row -/')
    out.append(f'theorem {tag}_logs : ∀ r ∈ {R}, ({Hlo} r.1 : ℝ) ≤ Real.log ((({m} : ℕ) : ℝ) / (r.1 : ℝ)) ∧')
    out.append(f'    Real.log ((({m} : ℕ) : ℝ) / (r.1 : ℝ)) ≤ {Hhi} r.1 := by')
    out.append('  intro r hr')
    out.append(f'  simp only [{R}, List.mem_cons, List.not_mem_nil, or_false] at hr')
    out.append('  ' + cases(len(data)))
    for t, n, c, lo, hi, _, _ in data:
        factors = [(BASIS[i], ci) for i, ci in enumerate(c) if ci]
        lst = ', '.join(f'(({nb} : ℝ) / {nb-1}, ({ci} : ℤ))' for nb, ci in factors)
        out.append('  · dsimp only')
        out.append(f'    have e : (({m} : ℕ) : ℝ) / (({t} : ℕ) : ℝ) = ([{lst}].map fun p => p.1 ^ p.2).prod := by')
        out.append('      norm_num')
        out.append(f'    rw [e, log_list _ (by norm_num)]')
        out.append(f'    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, {Hlo}, {Hhi}]')
        out.append('    push_cast')
        out.append('    constructor <;> linarith [' + ', '.join(
            f'(log_{nb}_{nb-1}).1, (log_{nb}_{nb-1}).2' for nb, _ in factors) + ']')
    out.append('')
    # numeric hints
    out.append('set_option maxHeartbeats 20000000 in')
    out.append(f'/-- {label}: the rational side conditions of `term_le` and `le_term` -/')
    out.append(f'theorem {tag}_hints : ∀ r ∈ {R}, 0 < r.1 ∧ r.1 < {m} ∧ 0 ≤ {Hlo} r.1 ∧')
    out.append(f'    {aname} * {Hhi} r.1 ≤ 1 ∧ P4 ({aname} * {Hhi} r.1) ≤ {U} r.1 ∧')
    out.append(f'    {D} r.1 ≤ S5 (({aname} + {lit(shift)}) * {Hlo} r.1) := by')
    out.append('  intro r hr')
    out.append(f'  simp only [{R}, List.mem_cons, List.not_mem_nil, or_false] at hr')
    out.append('  ' + cases(len(data)) + f' <;> norm_num [{Hlo}, {Hhi}, {U}, {D}, {aname}, P4, S5]')
    out.append('')
    out.append(f'/-- {label}: `Φ(a) < 1`, the source\'s moment test -/')
    out.append(f'theorem {tag}_moment : Φ {m} {W} {R} ({aname} : ℝ) < 1 := by')
    out.append(f'  apply moment_lt_one (U := fun t => ({U} t : ℝ)) (by norm_num)')
    out.append('  · intro r hr')
    out.append(f'    obtain ⟨h0, hm, -, h1, h2, -⟩ := {tag}_hints r hr')
    out.append(f'    exact term_le (by exact_mod_cast h0) (by exact_mod_cast hm.le) (by norm_num [{aname}])')
    out.append(f'      ({tag}_logs r hr).2 (by exact_mod_cast h1) (by unfold P4 at h2; exact_mod_cast h2)')
    out.append(f'  · simp only [{R}, {U}, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]')
    out.append('    norm_num')
    out.append('')
    out.append(f'/-- negative control: `Φ(a + {lit(shift)}) > 1`, so the moment test is tight -/')
    out.append(f'theorem {tag}_moment_tight : 1 < Φ {m} {W} {R} (({aname} : ℝ) + {lit(shift)}) := by')
    out.append(f'  rw [show ({aname} : ℝ) + {lit(shift)} = (({aname} + {lit(shift)} : ℚ) : ℝ) by push_cast; ring]')
    out.append(f'  apply one_lt_moment (D := fun t => ({D} t : ℝ)) (by norm_num)')
    out.append('  · intro r hr')
    out.append(f'    obtain ⟨h0, hm, hl, -, -, h3⟩ := {tag}_hints r hr')
    out.append(f'    exact le_term (by exact_mod_cast h0) (by exact_mod_cast hm.le) (by norm_num [{aname}])')
    out.append(f'      ({tag}_logs r hr).1 (by exact_mod_cast hl) (by unfold S5 at h3; exact_mod_cast h3)')
    out.append(f'  · simp only [{R}, {D}, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]')
    out.append('    norm_num')
    out.append('')
    return out


HEADER = '''import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import KappaCheck.CrocSwap

/-!
# Main's selected witness `κ = 25508460085039 / 5·10¹⁷`

Generated by `formal/lean/gen_selected.py` from `{arith}` and `{cxnet}`;
do not edit by hand.

* **A.** Moments as real-number inequalities. For each network,
  `Φ(a) = (1/W) Σ_t n_t (t/m)^(1-a) < 1` (`matrix-exponent-synthesis.tex`, eq. `moment`), with
  the bit saving `a_b` and the complex saving `a_c = 717/10⁷`. The proof bounds `log(m/t)` by
  series for `log(n/(n-1))` and `exp` by its Taylor bound. Negative controls: `Φ(a + shift) > 1`.
* **B.** The finite bridge: semantic constants, halving degrees, wire bits and the row gap,
  from their formulas in `balanced_assembly.py`.
* **C.** The 47 assembly slacks and seven margins, defined by `balanced_assembly.py`'s formulas
  over the parameters; all slacks are positive, the minimum margin is `G = εq`, and `κ < G`.
-/

namespace KappaCheck.Selected
open Real KappaCheck.CrocSwap

set_option maxRecDepth 100000

/-! ## A. Moments -/

/-- the moment `Φ(a) = (1/W) Σ_t n_t (t/m)^(1-a)` -/
noncomputable def Φ (m W : ℕ) (rows : List (ℕ × ℕ)) (a : ℝ) : ℝ :=
  (rows.map fun r => (r.2 : ℝ) * ((r.1 : ℝ) / m) ^ (1 - a)).sum / W

/-- `exp` upper bound from `Real.exp_bound'` with four terms -/
def P4 (v : ℚ) : ℚ := 1 + v + v ^ 2 / 2 + v ^ 3 / 6 + 5 * v ^ 4 / 96

/-- `exp` lower bound: its first five Taylor terms -/
def S5 (v : ℚ) : ℚ := 1 + v + v ^ 2 / 2 + v ^ 3 / 6 + v ^ 4 / 24

theorem exp_le_P4 {{v : ℝ}} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    exp v ≤ 1 + v + v ^ 2 / 2 + v ^ 3 / 6 + 5 * v ^ 4 / 96 := by
  have := Real.exp_bound' h0 h1 (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

theorem S5_le_exp {{v : ℝ}} (h0 : 0 ≤ v) :
    1 + v + v ^ 2 / 2 + v ^ 3 / 6 + v ^ 4 / 24 ≤ exp v := by
  have := Real.sum_le_exp_of_nonneg h0 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

theorem rpow_split {{m t a : ℝ}} (ht : 0 < t) (hm : 0 < m) :
    (t / m) ^ (1 - a) = t / m * exp (Real.log (m / t) * a) := by
  rw [Real.rpow_sub (div_pos ht hm), Real.rpow_one, div_eq_mul_inv (t / m),
    ← Real.inv_rpow (div_pos ht hm).le, inv_div, Real.rpow_def_of_pos (div_pos hm ht)]

/-- one term from above: `(t/m)^(1-a) ≤ (t/m)·U` -/
theorem term_le {{m t a H U : ℝ}} (ht : 0 < t) (htm : t ≤ m) (ha : 0 ≤ a)
    (hH : Real.log (m / t) ≤ H) (h1 : a * H ≤ 1)
    (hU : 1 + a * H + (a * H) ^ 2 / 2 + (a * H) ^ 3 / 6 + 5 * (a * H) ^ 4 / 96 ≤ U) :
    (t / m) ^ (1 - a) ≤ t / m * U := by
  have hm : 0 < m := lt_of_lt_of_le ht htm
  have hlog0 : 0 ≤ Real.log (m / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  rw [rpow_split ht hm]
  apply mul_le_mul_of_nonneg_left _ (div_pos ht hm).le
  calc exp (Real.log (m / t) * a) ≤ exp (a * H) := by
        apply Real.exp_le_exp.mpr; nlinarith
    _ ≤ _ := (exp_le_P4 (mul_nonneg ha (hlog0.trans hH)) h1).trans hU

/-- one term from below: `(t/m)·D ≤ (t/m)^(1-a)` -/
theorem le_term {{m t a H D : ℝ}} (ht : 0 < t) (htm : t ≤ m) (ha : 0 ≤ a)
    (hH : H ≤ Real.log (m / t)) (hH0 : 0 ≤ H)
    (hD : D ≤ 1 + a * H + (a * H) ^ 2 / 2 + (a * H) ^ 3 / 6 + (a * H) ^ 4 / 24) :
    t / m * D ≤ (t / m) ^ (1 - a) := by
  have hm : 0 < m := lt_of_lt_of_le ht htm
  rw [rpow_split ht hm]
  apply mul_le_mul_of_nonneg_left _ (div_pos ht hm).le
  calc D ≤ _ := hD
    _ ≤ exp (a * H) := S5_le_exp (mul_nonneg ha hH0)
    _ ≤ exp (Real.log (m / t) * a) := by apply Real.exp_le_exp.mpr; nlinarith

theorem moment_lt_one {{m W : ℕ}} {{rows : List (ℕ × ℕ)}} {{a : ℝ}} {{U : ℕ → ℝ}} (hW : 0 < W)
    (h : ∀ r ∈ rows, ((r.1 : ℝ) / m) ^ (1 - a) ≤ r.1 / m * U r.1)
    (hs : (rows.map fun r => (r.2 : ℝ) * (r.1 / m * U r.1)).sum < W) : Φ m W rows a < 1 := by
  unfold Φ
  rw [div_lt_one (by exact_mod_cast hW)]
  refine lt_of_le_of_lt (List.sum_le_sum fun r hr => ?_) hs
  exact mul_le_mul_of_nonneg_left (h r hr) (Nat.cast_nonneg _)

theorem one_lt_moment {{m W : ℕ}} {{rows : List (ℕ × ℕ)}} {{a : ℝ}} {{D : ℕ → ℝ}} (hW : 0 < W)
    (h : ∀ r ∈ rows, r.1 / m * D r.1 ≤ ((r.1 : ℝ) / m) ^ (1 - a))
    (hs : (W : ℝ) < (rows.map fun r => (r.2 : ℝ) * (r.1 / m * D r.1)).sum) : 1 < Φ m W rows a := by
  unfold Φ
  rw [one_lt_div (by exact_mod_cast hW)]
  refine lt_of_lt_of_le hs (List.sum_le_sum fun r hr => ?_)
  exact mul_le_mul_of_nonneg_left (h r hr) (Nat.cast_nonneg _)

theorem log_list (rs : List (ℝ × ℤ)) (hpos : ∀ p ∈ rs, 0 < p.1) :
    Real.log (rs.map fun p => p.1 ^ p.2).prod = (rs.map fun p => (p.2 : ℝ) * Real.log p.1).sum := by
  induction rs with
  | nil => simp
  | cons p rs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have h1 : 0 < p.1 := hpos p (by simp)
    have h2 : 0 < (rs.map fun p => p.1 ^ p.2).prod := by
      apply List.prod_pos
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact zpow_pos (hpos q (by simp [hq])) _
    rw [Real.log_mul (zpow_pos h1 _).ne' h2.ne', Real.log_zpow,
      ih (fun q hq => hpos q (by simp [hq]))]

'''


def basis_lean():
    out = ['/-! ### Basis logarithms `log(n/(n-1)) = -log(1 - 1/n)`, by `neglog_bounds` -/', '']
    for nb, n, lo, hi in BASIS_DATA:
        out.append(f'theorem log_{nb}_{nb-1} : ({lit(lo)} : ℝ) ≤ Real.log ({nb} / {nb-1}) ∧')
        out.append(f'    Real.log ({nb} / {nb-1}) ≤ ({lit(hi)} : ℝ) := by')
        out.append(f'  have e : Real.log ({nb} / {nb-1}) = -Real.log (1 - 1 / {nb}) := by')
        out.append('    rw [← Real.log_inv]; norm_num')
        out.append(f'  have h := neglog_bounds (1 / {nb}) (by norm_num) (by norm_num) {n}')
        out.append('  rw [e]; unfold ps at h')
        out.append('  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h')
        out.append('  constructor')
        out.append('  · refine le_trans ?_ h.1; norm_num')
        out.append('  · refine h.2.trans ?_; norm_num')
        out.append('')
    return out


def generate():
    a, bit, com = load()
    bdata = network('bit', bit, BIT_SHIFT)
    cdata = network('complex', com, CX_SHIFT)
    out = [HEADER.format(arith=ARITH, cxnet=CXNET)]
    out += basis_lean()
    out.append('/-! ### Parameters of the two moments -/')
    out.append('')
    out.append('/-- the bit saving `a_b` -/')
    out.append(f'def aB : ℚ := {lit(bit["a"])}')
    out.append('')
    out.append('/-- the complex saving `a_c` -/')
    out.append(f'def aC : ℚ := {lit(com["a"])}')
    out.append('')
    out.append('/-! ### Bit network (`m = 575`) -/')
    out.append('')
    out += network_lean('bit', 'bit network', bit, bdata, BIT_SHIFT, 'aB')
    out.append('/-! ### Complex network (`m = 784`) -/')
    out.append('')
    out += network_lean('cx', 'complex network', com, cdata, CX_SHIFT, 'aC')
    out.append(TAIL_TEMPLATE(a, bit, com))
    return '\n'.join(out)


def TAIL_TEMPLATE(a, bit, com):
    asm = a['assembly']
    fb = a['finite_bridge']
    sem = fb['semantic']
    cons = asm['constraints']
    names = list(cons)
    assert len(names) == 47
    slack_formula = {
        'a_positive': 'aB', 'a_below_b': 'aC - aB', 'b_below_one_over32': '1 / 32 - aC',
        'beta_positive': 'β', 'beta_below_one': '1 - β', 'phase_leaf_above_bit': '(1 - β) * aC - aB',
        'q_positive': 'q', 'q_below_internal': '1 - internal - q', 'q_below_leaf': '1 - leaf - q',
        'c_positive': 'c', 'c_below_one': '1 - c', 'q_below_reservations': 'c - q',
        'lambda_above_tau': 'lam - τ', 'lambda_above_sigma': 'lam - σ',
        'lambda_above_internal': 'lam - internal', 'lambda_prime_above_lambda': 'lp - lam',
        'compact_leaf': 'lp - leaf', 'compact_reservations': 'lp - (1 - c)',
        'lambda_prime_below_one': 'q', 'epsilon_positive': 'ε', 'epsilon_below_one': '1 - ε',
        'guard_width': '1 - ε * C1', 'K_geometry': '1 - ε * (1 + c)', 'K_dominates_log': 'ε * c',
        'record_suffix': '1 - ε', 'phase_local': '1 - ε - δ', 'phase_boundary': 'r - δ',
        'gamma_sublinear': '1 - ε - r', 'cell_above_band': 'ε - (1 - r) / 2',
        'prime_interval_packing': '1 - ε', 'alpha_positive': 'r', 'alpha_below_one': '1 - r',
        'alpha_below_one_fourth': '1 / 4 - r', 'delta_positive': 'δ',
        'delta_below_one_eighth': '1 / 8 - δ', 'short_record_fallback': 'ε - aB',
        'small_field_exposure': '1 - ε - G', 'artificial_boundary': '8 - ε + r - δ - G',
        'literal_scalar_guard': '(E : ℚ) - literal', 'row_product_gap': 'degreeGap'}
    margin_formula = dict(g1='1 - ε', g2='aB', g3='G', g4='aB', g5='min (1 - ε - δ) (r - δ)',
                          g6='1 - ε - δ', g7='ε')
    for g, f in margin_formula.items():
        slack_formula[g+'_above_kappa'] = f'{g} - κ'
    assert set(slack_formula) == set(names)
    p = asm['parameters']
    cb, cc = fb['bit'], fb['complex']
    L = []
    L.append('/-! ## B. Finite bridge (`balanced_assembly.py`, `validate_bridge`) -/')
    L.append('')
    L.append('/-- `halving_degree(m, child)`: the least `d ≥ 1` with `m^d > 2·child^d` -/')
    L.append('def IsHalvingDegree (m child d : ℕ) : Prop :=')
    L.append('  1 ≤ d ∧ 2 * child ^ d < m ^ d ∧ ∀ k, 1 ≤ k → k < d → m ^ k ≤ 2 * child ^ k')
    L.append('')
    for tag, d in (('bit', cb), ('cx', cc)):
        L.append(f'theorem {tag}_halving : IsHalvingDegree {d["m"]} {d["maxchild"]} {d["halving_degree"]} := by')
        L.append('  refine ⟨by norm_num, by norm_num, fun k h1 h2 => ?_⟩')
        L.append('  interval_cases k <;> norm_num')
        L.append('')
    L.append('/-- `W.bit_length()` for both networks, and the largest child of each row list -/')
    L.append(f'theorem wire_bits : 2 ^ {cb["wire_bits"]-1} ≤ {cb["W"]} ∧ {cb["W"]} < 2 ^ {cb["wire_bits"]} ∧')
    L.append(f'    2 ^ {cc["wire_bits"]-1} ≤ {cc["W"]} ∧ {cc["W"]} < 2 ^ {cc["wire_bits"]} ∧')
    L.append(f'    (bitRows.map Prod.fst).max? = some {cb["maxchild"]} ∧')
    L.append(f'    (cxRows.map Prod.fst).max? = some {cc["maxchild"]} := by')
    L.append('  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, by decide⟩')
    L.append('')
    L.append('/-- rank mass: `Σ t n_t = s`, with `s_b = W m - N + L` (copied centres) -/')
    L.append(f'theorem rank_mass : (bitRows.map fun r => r.1 * r.2).sum = {bit["W"]} * {bit["m"]} - {bit["N"]} + {bit["L"]} ∧')
    L.append(f'    (cxRows.map fun r => r.1 * r.2).sum = {cc["s"]} := by')
    L.append('  constructor <;> decide')
    L.append('')
    L.append(f'def mC : ℕ := {cc["m"]}')
    L.append(f'def WC : ℕ := {cc["W"]}')
    L.append(f'def childC : ℕ := {cc["maxchild"]}')
    L.append(f'def sC : ℕ := {cc["s"]}')
    L.append('/-- `scalar_group_upper`: supplied by the producer, not recomputed (as in the script) -/')
    L.append(f'def scalar : ℕ := {cc["scalar_group_upper"]}')
    L.append('def E : ℕ := 64 * (WC + mC + scalar + 1) ^ 3')
    L.append('def Bs : ℕ := sC + E')
    L.append('def literal : ℕ := 2 * scalar * WC ^ 2 + 8 * sC + 4 * WC + 4 + 32 * mC')
    L.append('def C0 : ℕ := 32 * mC * Bs ^ 2')
    L.append('def inductionGap : ℤ := 2 * Bs * (mC - childC : ℤ) - (sC + E)')
    L.append(f'def coefficient : ℕ := {cb["halving_degree"]} * {cb["wire_bits"]} + {cc["halving_degree"]} * {cc["wire_bits"]}')
    L.append(f'def degree : ℕ := {fb["rows"]["degree"]}')
    L.append('def degreeGap : ℚ := degree - 51 / 25 * coefficient')
    L.append('')
    L.append('/-- the semantic constants and row constants, with the script\'s three requirements -/')
    L.append(f'theorem semantic_values : E = {sem["E"]} ∧ Bs = {sem["B"]} ∧')
    L.append(f'    literal = {sem["literal_charge"]} ∧ C0 = {sem["C0"]} ∧')
    L.append(f'    E - literal = {sem["strict_literal_gap"]} ∧ inductionGap = {sem["induction_gap"]} ∧')
    L.append(f'    coefficient = {fb["rows"]["coefficient"]} ∧ degreeGap = {lit(Q(fb["rows"]["degree_gap"]))} ∧')
    L.append('    literal < E ∧ 0 ≤ inductionGap ∧ 2 * Bs + 18 < C0 ∧ 0 < sC ∧ sC < mC * WC ∧ 0 < degreeGap := by')
    L.append('  norm_num [E, Bs, literal, C0, inductionGap, coefficient, degree, degreeGap, mC, WC, childC, sC, scalar]')
    L.append('')
    L.append('/-! ## C. Assembly (`balanced_assembly.py`, `assembly`) -/')
    L.append('')
    L.append(f'def κ : ℚ := {lit(Q(a["kappa"]))}')
    L.append(f'def β : ℚ := {lit(Q(p["beta"]))}')
    L.append(f'def hB : ℚ := {lit(Q(a["h_backoff"]))}')
    L.append('def τ : ℚ := 1 - aB')
    L.append('def σ : ℚ := 1 - aC')
    L.append('def q : ℚ := aB * (1 - 2 * hB)')
    L.append('def lp : ℚ := 1 - q')
    L.append('def c : ℚ := q + hB / 4')
    L.append('def ε : ℚ := (1 - hB) / (1 + q)')
    L.append('def lam : ℚ := (τ + lp) / 2')
    L.append('def G : ℚ := ε * q')
    L.append('def r : ℚ := (G + 1 - ε) / 2')
    L.append('def δ : ℚ := hB / 8')
    L.append('def C1 : ℚ := 1')
    L.append('def internal : ℚ := τ + (1 - β) * max (σ - τ) 0')
    L.append('def leaf : ℚ := σ + β * (1 - σ)')
    for g, f in margin_formula.items():
        L.append(f'def {g} : ℚ := {f}')
    L.append('')
    L.append('/-- the seven margins, in the script\'s order -/')
    L.append('def margins : List (String × ℚ) := [' + ', '.join(f'("{g}", {g})' for g in margin_formula) + ']')
    L.append('')
    L.append('/-- the 47 strict slacks, in the script\'s order -/')
    L.append('def slacks : List (String × ℚ) := [')
    L.append(',\n'.join(f'  ("{n}", {slack_formula[n]})' for n in names) + ']')
    L.append('')
    simp = 'max_def, min_def, aB, aC, κ, β, hB, τ, σ, q, lp, c, ε, lam, G, r, δ, C1, internal, leaf, g1, g2, g3, g4, g5, g6, g7'
    L.append('/-- every parameter equals the certificate\'s value -/')
    L.append('theorem parameter_values : ' + ' ∧\n    '.join(
        f'{v} = {lit(Q(p[k]))}' for v, k in (('τ', 'tau'), ('σ', 'sigma'), ('q', 'q'), ('c', 'c'),
                                              ('ε', 'epsilon'), ('lam', 'lambda_'), ('lp', 'lambda_prime'),
                                              ('r', 'alpha_squared_power'), ('δ', 'delta'), ('κ', 'kappa'))) + ' := by')
    L.append(f'  norm_num [{simp}]')
    L.append('')
    L.append('/-- every slack equals the certificate\'s value -/')
    L.append('theorem slack_values : slacks = [')
    L.append(',\n'.join(f'  ("{n}", {lit(Q(cons[n]))})' for n in names) + '] := by')
    L.append(f'  simp only [slacks, {simp}, E, literal, WC, mC, sC, scalar, degreeGap, degree, coefficient]')
    L.append('  norm_num')
    L.append('')
    L.append('/-- every margin equals the certificate\'s value -/')
    L.append('theorem margin_values : margins = [' + ', '.join(
        f'("{g}", {lit(Q(asm["margins"][g]))})' for g in margin_formula) + '] := by')
    L.append(f'  simp only [margins, {simp}]')
    L.append('  norm_num')
    L.append('')
    L.append('theorem slacks_length : slacks.length = 47 ∧ margins.length = 7 := ⟨rfl, rfl⟩')
    L.append('')
    L.append('/-- all 47 slacks are positive -/')
    L.append('theorem slacks_pos : ∀ s ∈ slacks, 0 < s.2 := by')
    L.append('  rw [slack_values]')
    L.append('  simp only [List.mem_cons, List.not_mem_nil, or_false]')
    L.append('  rintro s (' + ' | '.join(['rfl']*47) + ') <;> norm_num')
    L.append('')
    L.append('/-- the minimum margin is `G = εq`, and `κ < G` -/')
    L.append('theorem kappa_below_margins : (∀ g ∈ margins, G ≤ g.2) ∧ ("g3", G) ∈ margins ∧ κ < G := by')
    L.append('  refine ⟨?_, by simp [margins, g3], ?_⟩')
    L.append('  · rw [margin_values]; simp only [List.mem_cons, List.not_mem_nil, or_false]')
    L.append(f'    rintro g ({" | ".join(["rfl"]*7)}) <;> norm_num [{simp}]')
    L.append(f'  · norm_num [{simp}, max_def, min_def]')
    L.append('')
    L.append('/-- the script\'s balanced identities -/')
    L.append('theorem balanced_identities : 1 - ε - G = hB ∧ 1 - ε - r = hB / 2 ∧')
    L.append('    1 - ε * (1 + c) = hB - ε * hB / 4 := by')
    L.append(f'  norm_num [{simp}]')
    L.append('')
    L.append('/-- κ against the published witness, its old scoped limit, the new scoped limit and `2⁻¹⁵`;')
    L.append('the absorption gap; negative control: the next κ grid value fails `g3` -/')
    cmp = a['comparison']
    L.append(f'theorem kappa_facts : ({lit(Q(cmp["old_published_kappa"]))} : ℚ) < κ ∧')
    L.append(f'    ({lit(Q(cmp["old_formal_scoped_limit"]))} : ℚ) < κ ∧ κ < aB / (1 + aB) ∧')
    L.append(f'    aB / (1 + aB) = {lit(Q(asm["scoped_limit"]))} ∧ (1 : ℚ) / 2 ^ 15 < κ ∧')
    L.append(f'    G - κ = {lit(Q(asm["absorption_gap"]))} ∧ G < κ + {lit(Q(1, Q(a["kappa"]).denominator))} := by')
    L.append(f'  norm_num [{simp}]')
    L.append('')
    L.append('/-- **The selected certificate.** Both moments hold as real inequalities at the savings')
    L.append('the slacks use (`τ = 1 - a_b`, `σ = 1 - a_c`), all 47 slacks are positive and `κ` lies')
    L.append('below every margin. -/')
    L.append(f'theorem selected_certificate : Φ {bit["m"]} {bit["W"]} bitRows (aB : ℝ) < 1 ∧')
    L.append(f'    Φ {com["m"]} {com["W"]} cxRows (aC : ℝ) < 1 ∧ τ = 1 - aB ∧ σ = 1 - aC ∧')
    L.append('    (∀ s ∈ slacks, 0 < s.2) ∧ ∀ g ∈ margins, κ < g.2 := by')
    L.append('  refine ⟨bit_moment, cx_moment, rfl, rfl, slacks_pos, fun g hg => ?_⟩')
    L.append('  exact lt_of_lt_of_le kappa_below_margins.2.2 (kappa_below_margins.1 g hg)')
    L.append('')
    L.append('end KappaCheck.Selected')
    L.append('')
    return '\n'.join(L)


if __name__ == '__main__':
    text = generate()
    if '--check' in sys.argv:
        ok = OUT.exists() and OUT.read_text() == text
        print('OK: Selected.lean is current' if ok else 'Selected.lean is stale: run gen_selected.py')
        sys.exit(0 if ok else 1)
    OUT.write_text(text)
    print(f'wrote {OUT}')
