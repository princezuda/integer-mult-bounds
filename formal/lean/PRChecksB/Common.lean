import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Shared lemmas for the PR #5, #6, #7 arithmetic checks

`exponent_certificate`, `log_le_of_pow`, `log_split`, `L25`, `log_15625_note`,
`log_125000`, `ps` and `neglog_bounds` are copied verbatim (up to namespace) from
`formal/lean/KappaCheck/{Certificates,CrocSwap}.lean` on branch `lean-certificate-check`
of CrocSwap/integer-mult-bounds (commit f99d715), so that this project does not
depend on that branch.

New here: `log_21952` (the `h = 28` label dimension of PR #7), `log_125000_gt`, `log_prod`,
`certified_saving_le`, the parameter record `Params` with the compact-control recurrence
exponents, the seven margins in both Gaussian models and the 29 fast slacks (`FastOK`), and
the generic scoped-ceiling inequalities.
-/

namespace PRChecksB

open Real

/-! ## The generic exponent certificate (copied from `KappaCheck.Certificates`) -/

/-- If `x > 0`, `x * L ≤ η`, `log m < L`, `m > 0` and `r = m (1 - η)`, then
`r < m ^ (1 - x)`. -/
theorem exponent_certificate (m L x η r : ℝ) (hm : 0 < m) (hx : 0 < x)
    (hlog : Real.log m < L) (hxη : x * L ≤ η) (hr : r = m * (1 - η)) :
    r < m ^ (1 - x) := by
  have hpow : m ^ (1 - x) = m * Real.exp (-(Real.log m * x)) := by
    rw [Real.rpow_sub hm, Real.rpow_one, Real.rpow_def_of_pos hm, Real.exp_neg, div_eq_mul_inv]
  have hexp := Real.add_one_le_exp (-(Real.log m * x))
  have h1 : Real.log m * x < L * x := mul_lt_mul_of_pos_right hlog hx
  have h3 : 1 - η < Real.exp (-(Real.log m * x)) := by nlinarith
  rw [hpow, hr]
  exact mul_lt_mul_of_pos_left h3 hm

/-! ## Logarithm bounds (copied from `KappaCheck.CrocSwap`) -/

theorem log_le_of_pow (y q : ℝ) (n : ℕ) (hy : 0 < y) (hq : 0 < q) (hq1 : q ≠ 1) (hn : 0 < n)
    (h : y ≤ q ^ n) : Real.log y < n * (q - 1) := by
  calc Real.log y ≤ Real.log (q ^ n) := Real.log_le_log hy h
    _ = n * Real.log q := by rw [Real.log_pow]
    _ < n * (q - 1) := by
        gcongr; exact Real.log_lt_sub_one_of_pos hq hq1

theorem log_split (k : ℕ) :
    Real.log (2 ^ k * (15625 / 16384)) <
      k * (6931471808 / 10 ^ 10) + 256 * ((9998147318001 : ℝ) / 10 ^ 13 - 1) := by
  have hy := log_le_of_pow (15625 / 16384) ((9998147318001 : ℝ) / 10 ^ 13) 256
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  push_cast at hy ⊢
  have : (k : ℝ) * Real.log 2 ≤ k * (6931471808 / 10 ^ 10) := by
    have : Real.log 2 ≤ 6931471808 / 10 ^ 10 := by norm_num at h2 ⊢; linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  linarith

def L25 : ℚ := 14 * (6931471808 / 10 ^ 10) + 256 * (9998147318001 / 10 ^ 13 - 1)  -- audit

theorem log_15625 : Real.log 15625 < (L25 : ℝ) := by
  have := log_split 14
  rw [show (2 : ℝ) ^ 14 * (15625 / 16384) = 15625 by norm_num] at this
  unfold L25; push_cast; linarith

/-- `log 15625 < 966/100 = 483/50` (h = 25 complex network) -/
theorem log_15625_note : Real.log 15625 < 966 / 100 := by
  have h := log_15625
  have : (L25 : ℝ) < 966 / 100 := by unfold L25; norm_num
  linarith

/-- `log 125000 < 11737/1000` (h = 50 bit network) -/
theorem log_125000 : Real.log 125000 < 11737 / 1000 := by
  have := log_split 17
  rw [show (2 : ℝ) ^ 17 * (15625 / 16384) = 125000 by norm_num] at this
  norm_num at this ⊢; linarith

/-- partial sums of `-log(1 - x)` -/
noncomputable def ps (x : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)

theorem neglog_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ps x n - x ^ (n + 1) / (1 - x) ≤ -Real.log (1 - x) ∧
    -Real.log (1 - x) ≤ ps x n + x ^ (n + 1) / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |x| < 1 by rw [abs_of_nonneg hx0]; exact hx1) n
  rw [abs_of_nonneg hx0] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  unfold ps; constructor <;> linarith

/-! ## New: `log 21952 < 9997/1000` for `m = 28³` (PR #7)

`21952 = 2^15 (1 - 1/8)^3`, so `log 21952 = 15 log 2 - 3 (-log(1 - 1/8))`, with
`log 2 < 0.6931471808` and the series lower bound for `-log(7/8)`. The bound has
room `≈ 3.7·10⁻⁴` (`log 21952 ≈ 9.9966135`). -/

theorem log_21952 : Real.log 21952 < 9997 / 1000 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hb := (neglog_bounds (1 / 8) (by norm_num) (by norm_num) 5).1
  have hsplit : Real.log 21952 = 15 * Real.log 2 + 3 * Real.log (1 - 1 / 8) := by
    rw [show (21952 : ℝ) = 2 ^ 15 * (1 - 1 / 8) ^ 3 by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  unfold ps at hb
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
  norm_num at hb h2 ⊢
  rw [hsplit]
  linarith

theorem log_21952_lt_10 : Real.log 21952 < 10 := by
  have := log_21952; linarith

/-! ## New: `log 125000 > 11.7349`, exact `log` products, certified-saving bound -/

/-- `125000 = 2^17 · 125000/131072` and `log y ≥ 1 - 1/y` (as `PRChecksA.Bit.log_125000_gt`) -/
theorem log_125000_gt : (117349 : ℝ) / 10000 < Real.log 125000 := by
  have h2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hy : (0 : ℝ) < 125000 / 131072 := by norm_num
  have hl : 1 - 1 / (125000 / 131072 : ℝ) ≤ Real.log (125000 / 131072) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (125000 / 131072) by positivity)
    rw [one_div, Real.log_inv] at this
    rw [one_div]; linarith
  have e : Real.log 125000 = 17 * Real.log 2 + Real.log (125000 / 131072) := by
    rw [show (125000 : ℝ) = 2 ^ 17 * (125000 / 131072) by norm_num,
      Real.log_mul (by positivity) hy.ne', Real.log_pow]
    push_cast; ring_nf
  norm_num at h2 hl
  rw [e]; linarith

/-- `log M = a A + b B + c C` for `M = (16/15)^a (25/24)^b (81/80)^c`, `A = -log(15/16)`, … -/
theorem log_prod (a b c : ℕ) (M : ℝ)
    (hM : M = (1 / (1 - 1 / 16)) ^ a * (1 / (1 - 1 / 25)) ^ b * (1 / (1 - 1 / 81)) ^ c) :
    Real.log M = a * -Real.log (1 - 1 / 16) + b * -Real.log (1 - 1 / 25) +
      c * -Real.log (1 - 1 / 81) := by
  rw [hM, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  simp only [one_div, Real.log_inv]

/-- a certified `σ` (`r ≤ m^σ`) has `(1-σ) log m ≤ (1 - r/m)/(r/m)` (main's
`certified_saving_le`) -/
theorem certified_saving_le (m r σ' : ℝ) (hm : 1 < m) (hr : 0 < r)
    (hcert : r ≤ m ^ σ') :
    (1 - σ') * Real.log m ≤ (1 - r / m) / (r / m) := by
  have hm0 : 0 < m := by linarith
  have hlog : Real.log r ≤ σ' * Real.log m := by
    have := Real.log_le_log hr hcert
    rwa [Real.log_rpow hm0] at this
  have hq : 0 < r / m := div_pos hr hm0
  have key : -Real.log (r / m) ≤ (1 - r / m) / (r / m) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hq)
    rw [Real.log_inv] at this
    have e : (1 - r / m) / (r / m) = (r / m)⁻¹ - 1 := by field_simp
    rw [e]; linarith
  rw [Real.log_div hr.ne' hm0.ne'] at key
  nlinarith

/-! ## Parameters, recurrence exponents and margins

`internal`, `leaf`, `prep`, `layer` are `scripts/compact_control_layer.py`,
`layer_exponents` (with `theta = 0`, i.e. compact controls). `g1 … g7` are
`scripts/certify.py`, `margins(…, 'nonadjacent', 'tight-gaussian')`; `g5fast` is the
replacement `1 - δ - 2ε` of `scripts/fast_gaussian.py`, `fast_margins`. -/

structure Params where
  τ : ℚ
  σ : ℚ
  ε : ℚ
  c : ℚ
  lam : ℚ
  lamp : ℚ
  κ : ℚ
  β : ℚ
  δ : ℚ
  C1 : ℚ

namespace Params

variable (p : Params)

def internal : ℚ := p.τ + (1 - p.β) * max (p.σ - p.τ) 0
def leaf : ℚ := p.σ + p.β * (1 - p.σ)
def prep : ℚ := max 0 (1 - p.c)
def layer : ℚ := max (max p.internal p.leaf) (max (1 - p.c) 0)

def g1 : ℚ := 1 - p.ε * (1 + p.c)
def g2 : ℚ := p.ε * p.c * (1 - p.τ)
def g3 : ℚ := p.ε * (1 - p.lamp)
def g4 : ℚ := 1 - p.τ - p.ε * (1 - p.τ)
/-- tight-Gaussian `g5` (retained Gaussian maps; used by the 59/10¹¹ witness) -/
def g5tight : ℚ := 1 / 4 - p.δ - 5 / 4 * p.ε
/-- fast-Gaussian `g5 = 1 - δ - 2ε` (PR #5) -/
def g5fast : ℚ := 1 - p.δ - 2 * p.ε
def g6 : ℚ := 1 - p.δ - p.ε
def g7 : ℚ := p.ε

/-- the 29 fast-Gaussian slacks (`fast_constraints` plus the compact-control rows), as
listed in `PR5.Fast.constraint_slacks` -/
def FastOK : Prop :=
  0 < p.ε * p.c ∧ 0 < 1 - p.ε - p.ε * p.c ∧ 0 < 1 - 2 * p.ε ∧ 0 < 1 - p.β ∧ 0 < p.β ∧
  0 < p.c ∧ 0 < 1 - p.τ - p.ε * (1 - p.τ) ∧ 0 < 1 / 8 - p.δ ∧ 0 < p.δ ∧ 0 < p.ε ∧
  0 < 1 - p.δ - 2 * p.ε ∧ 0 < 1 - p.ε * p.C1 ∧ 0 < p.κ ∧ 0 < p.lam - p.σ ∧
  0 < p.lam - p.τ ∧ 0 < 1 - p.lam ∧ 0 < p.lamp - p.lam ∧ 0 < 1 - p.lamp ∧
  0 < p.lamp - (p.σ + p.β * (1 - p.σ)) ∧ 0 < p.lam - p.internal ∧
  0 < 1 - p.ε * (1 + p.c) ∧ 0 < 1 - 2 * p.ε ∧ 0 < 1 - p.ε ∧ 0 < p.lamp - p.prep ∧
  0 < 1 - p.δ - p.ε ∧ 0 < 1 - p.σ ∧ 0 < p.σ ∧ 0 < 1 - p.τ ∧ 0 < p.τ

/-- `κ` is below all seven fast-Gaussian margins -/
def FastAbsorbs : Prop :=
  p.κ < p.g1 ∧ p.κ < p.g2 ∧ p.κ < p.g3 ∧ p.κ < p.g4 ∧ p.κ < p.g5fast ∧ p.κ < p.g6 ∧ p.κ < p.g7

end Params

/-! ## Generic scoped-ceiling inequalities -/

/-- Fast-Gaussian ceiling (PR #5 note, "The next ceiling"; PR #6): if `λ' > τ`,
`ε > 0` and `κ` is below `g3 = ε(1-λ')` and `g4 = (1-τ)(1-ε)`, then `κ < (1-τ)/2`.
Only `g3` and `g4` are needed. -/
theorem ceiling_half (τ' ε' lamp' κ' : ℝ) (hτ : τ' < 1) (hl : τ' < lamp') (hε : 0 < ε')
    (h3 : κ' < ε' * (1 - lamp')) (h4 : κ' < (1 - τ') * (1 - ε')) : κ' < (1 - τ') / 2 := by
  rcases le_or_gt ε' (1 / 2) with h | h
  · have : ε' * (1 - lamp') < ε' * (1 - τ') := by nlinarith
    nlinarith
  · nlinarith

/-- the correct form of "g2, g3, g4 ≤ a·min(ε, 1-ε)": the *minimum* of `g3, g4` is at most
`a·min(ε, 1-ε)` with `a = 1 - τ` (each margin separately need not be) -/
theorem min_g3_g4_le (τ' ε' lamp' : ℝ) (hl : τ' < lamp') (hε : 0 < ε') :
    min (ε' * (1 - lamp')) ((1 - τ') * (1 - ε')) ≤ (1 - τ') * min ε' (1 - ε') := by
  rcases le_total ε' (1 - ε') with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by nlinarith)
  · rw [min_eq_right h]
    exact min_le_right _ _

/-- Tight-Gaussian ceiling with a binding bit network (PR #3 note in PR #5's base,
"The next ceiling"): `0 < 1/4 - δ - 5ε/4`, `δ ≥ 0`, `λ' > τ`, `κ < ε(1-λ')` give
`κ < (1-τ)/5`. -/
theorem ceiling_fifth (τ' ε' δ' lamp' κ' : ℝ) (hτ : τ' < 1) (hδ : 0 ≤ δ')
    (hgauss : 0 < 1 / 4 - δ' - 5 / 4 * ε') (hl : τ' < lamp') (hε : 0 < ε')
    (h3 : κ' < ε' * (1 - lamp')) : κ' < (1 - τ') / 5 := by
  have h1 : ε' < 1 / 5 := by linarith
  have : ε' * (1 - lamp') < ε' * (1 - τ') := by nlinarith
  nlinarith

end PRChecksB
