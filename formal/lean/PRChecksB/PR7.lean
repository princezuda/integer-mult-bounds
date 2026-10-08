import PRChecksB.Common

/-!
# PR #7 (ternary five-subset witness, κ = 373/10¹¹ > 2^-28): certificate arithmetic

Source: `certificates/prime-field28.json`, written by `scripts/prime_field_network.py`,
in worktree `/home/user/prs/pr7` (head `6725c6a`, base `6e56487`); notes
`notes/prime-field28-note.tex`, `notes/prime-field28-construction.tex`,
`docs/research/prime-field28.md`. (`fast-gaussian.json` in this branch is byte-identical
to PR #5's and is checked by `PRChecksB.PR5`.)

* **A.** the F₃ five-subset bit network at `h = 28`, *given* the producer's role bound
  `R_b = 11840940` (from the C++ support/template checker; taken as given):
  `W_b = 2v²(v+R_b)`, `L_b = 3v²C(h,2)(h-2)`, `D = N - 2L_b`, `s_b = W_b m - D`,
  `η_b = 39/520019360`, `log 21952 < 9997/1000`, `s_b/W_b < 21952^τ`, `1-τ = 3/(4·10⁸)`;
  and the producer bookkeeping that composes `R_b` from the certified addition counts.
* **B.** the paired complex network at `h = 28`, *given* `R_c = 93838` roles and `61022`
  additions (from `PairedComplex(28)`; taken as given): counts, `η_c = 5/12693352`,
  `log 21952 < 10`, `s_c/W_c < 21952^σ`, `1-σ = 39/10⁹`, the `12W` gate bound, the guard
  constants and the coefficient-depth enclosure `36W³ + 4s + 4W + 4 < E`.
* **C.** the witness: 29 fast-Gaussian slacks, margins, `min g = g3 = 934813/(25·10¹³)`,
  `2^-28 < κ < 2^-27`.
* **D.** small algebraic claims of the construction note and the `h = 8` control counts.
-/

namespace PRChecksB.PR7

open Real

/-! ## A. The five-subset bit network -/

/-- role upper bound of the producer (`independent_template_check.role_upper_bound`):
**taken as given** (from running the C++ checker) -/
def Rb : ℕ := 11840940  -- json prime-field28.json witness.bit.roles

/-- the certified bit saving `a_b = 3/(4·10⁸)` -/
def aB : ℚ := 3 / 400000000  -- json prime-field28.json witness.constraints.tau_below_one

def v : ℕ := Nat.choose 28 5
def m : ℕ := 28 ^ 3  -- json prime-field28.json witness.bit.m
def N : ℕ := v ^ 3
def c2 : ℕ := Nat.choose 28 2
/-- `W = 2v²(v + R)` (`bit_counts`) -/
def Wb : ℕ := 2 * v ^ 2 * (v + Rb)
/-- `L = 3v²·C(h,2)·(h-2)`: each retained total loses `h - 2` -/
def Lb : ℕ := 3 * v ^ 2 * c2 * (28 - 2)
def Db : ℕ := N - 2 * Lb
def sb : ℕ := Wb * m - Db

theorem v_eq : v = 98280 := by decide
theorem c2_eq : c2 = 378 := by decide

theorem bit_counts :
    v = 98280 ∧  -- json prime-field28.json witness.bit.v
    m = 21952 ∧  -- json prime-field28.json witness.bit.m
    N = 949282431552000 ∧  -- json prime-field28.json witness.bit.N
    c2 = 378 ∧  -- json prime-field28.json witness.bit.retained_totals
    Wb = 230640858616896000 ∧  -- json prime-field28.json witness.bit.W
    Lb = 284784729465600 ∧  -- json prime-field28.json witness.bit.L
    Db = 379712972620800 ∧  -- json prime-field28.json witness.bit.D
    sb = 5063027748645128371200 ∧  -- json prime-field28.json witness.bit.s
    2 * Lb < N ∧ Db ≤ Wb * m ∧
    -- the note's form `s_b = W_b m - N + 2L_b` (construction lines 157-159)
    sb = Wb * m + 2 * Lb - N := by
  simp only [Wb, Lb, Db, sb, N, m, Rb, v_eq, c2_eq]; norm_num

theorem bit_eta :
    ((Db : ℕ) : ℚ) / (Wb * m) = 39 / 520019360  -- json prime-field28.json witness.bit.eta
    := by
  simp only [Wb, Lb, Db, N, m, Rb, v_eq, c2_eq]; norm_num

theorem bit_deficit_slack :
    (39 / 520019360 : ℚ) - aB * (9997 / 1000) =
      25621089 / 1300048400000000000  -- json prime-field28.json witness.deficit_slacks.bit
    := by norm_num [aB]

theorem bit_log : Real.log 21952 < 9997 / 1000  -- json prime-field28.json witness.log_upper.bit
    := log_21952

/-- **exponent certificate**: `s_b / W_b < 21952 ^ (1 - a_b)` -/
theorem bit_exponent :
    ((sb : ℕ) : ℝ) / (Wb : ℕ) < (21952 : ℝ) ^ (1 - (aB : ℝ)) := by
  obtain ⟨-, -, -, -, hW, -, -, hs, -⟩ := bit_counts
  rw [hs, hW, show ((aB : ℚ) : ℝ) = 3 / 400000000 by norm_num [aB]]
  apply exponent_certificate 21952 (9997 / 1000) (3 / 400000000) (39 / 520019360) _
    (by norm_num) (by norm_num) log_21952
  · norm_num
  · norm_num

/-! ### Producer bookkeeping (counts from the checker: **taken as given**) -/

def localAdd : ℕ := 41427  -- json prime-field28.json producer.local.additions
def localRetained : ℕ := 41439  -- json prime-field28.json producer.local.retained_additions
def localRoles : ℕ := 44027  -- json prime-field28.json producer.local.roles
def globalAdd : ℕ := 11240978  -- json prime-field28.json producer.global_before_replacement.unique_additions
def globalOut : ℕ := 983178  -- json prime-field28.json producer.global_before_replacement.outputs
def globalRoles : ℕ := 12224156  -- json prime-field28.json producer.global_before_replacement.roles
def oldStar : ℕ := 3006276  -- json prime-field28.json producer.replacements.old_additions
def newStar : ℕ := 2623060  -- json prime-field28.json producer.replacements.new_additions
def savedStar : ℕ := 383216  -- json prime-field28.json producer.replacements.saved
def optAdd : ℕ := 10857762  -- json prime-field28.json producer.independent_template_check.optimized_additions
def stars : ℕ := 20475  -- json prime-field28.json producer.replacements.stars
def matchDomain : ℕ := 98280  -- json prime-field28.json matching.domain

/-- `c = 10857762`, `q = 10v + C(h,2) = 983178`, `R = c + q = 11840940` (construction lines
37-47 and 68-76), one star per four-set, one matching image per five-set -/
theorem producer_arith :
    Nat.choose 26 3 = 2600 ∧ localRoles = localAdd + Nat.choose 26 3 ∧
    localRetained = localAdd + 12 ∧ globalOut = 10 * v + c2 ∧
    globalRoles = globalAdd + globalOut ∧ savedStar = oldStar - newStar ∧
    optAdd = globalAdd - oldStar + newStar ∧ Rb = optAdd + globalOut ∧
    stars = Nat.choose 28 4 ∧ matchDomain = v := by
  have h26 : Nat.choose 26 3 = 2600 := by decide
  have h28 : Nat.choose 28 4 = 20475 := by decide
  simp only [h26, h28, localRoles, localAdd, localRetained, globalOut, globalRoles, globalAdd,
    savedStar, oldStar, newStar, optAdd, Rb, stars, matchDomain, v_eq, c2_eq]
  norm_num

/-! ## B. The paired complex network -/

/-- roles of `PairedComplex(28)`: **taken as given** -/
def Rc : ℕ := 93838  -- json prime-field28.json witness.complex.roles
def cxAdd : ℕ := 61022  -- json prime-field28.json complex_checks.stats.additions
def cxInj : ℕ := 32816  -- json prime-field28.json complex_checks.stats.injections
def cxDisj : ℕ := 43634  -- json prime-field28.json complex_checks.stats.disjoint_additions
def cxStar : ℕ := 17388  -- json prime-field28.json complex_checks.stats.pair_star_additions

/-- the certified complex saving `a_c = 39/10⁹` -/
def aC : ℚ := 39 / 1000000000  -- json prime-field28.json witness.constraints.sigma_below_one

def vc : ℕ := Nat.choose 28 3
def Nc : ℕ := vc ^ 3
def Ic : ℕ := 3 * vc ^ 2
/-- `W_c = 2v²(v + R + h + 1)` (complete stage-1/3 bank sharing, PR #4) -/
def Wc : ℕ := 2 * vc ^ 2 * (vc + Rc + 28 + 1)
def Lc : ℕ := Ic * 28 * (28 + 1)
def Dc : ℕ := 2 * Nc - 2 * Lc
def sc : ℕ := Wc * m - Dc

theorem vc_eq : vc = 3276 := by decide

theorem complex_counts :
    vc = 3276 ∧  -- json prime-field28.json witness.complex.v
    Nc = 35158608576 ∧  -- json prime-field28.json witness.complex.N
    Ic = 32196528 ∧  -- json prime-field28.json witness.complex.I
    Wc = 2085111546336 ∧  -- json prime-field28.json witness.complex.W
    Lc = 26143580736 ∧  -- json prime-field28.json witness.complex.L
    Dc = 18030055680 ∧  -- json prime-field28.json witness.complex.D
    sc = 45772350635112192 ∧  -- json prime-field28.json witness.complex.s
    m = 21952 ∧  -- json prime-field28.json witness.complex.m
    Lc < Nc ∧ Dc ≤ Wc * m ∧
    -- the note's `s_c = W_c m_c - 2v_c³ + 2L_c`
    sc = Wc * m + 2 * Lc - 2 * Nc ∧
    Rc = cxAdd + cxInj ∧ cxAdd = cxDisj + cxStar := by
  simp only [Wc, Lc, Dc, sc, Nc, Ic, m, Rc, cxAdd, cxInj, cxDisj, cxStar, vc_eq]; norm_num

theorem complex_eta :
    ((Dc : ℕ) : ℚ) / (Wc * m) = 5 / 12693352  -- json prime-field28.json witness.complex.eta
    := by
  simp only [Wc, Lc, Dc, Nc, Ic, m, Rc, vc_eq]; norm_num

theorem complex_deficit_slack :
    (5 / 12693352 : ℚ) - aC * 10 =
      619909 / 158666900000000  -- json prime-field28.json witness.deficit_slacks.complex
    := by norm_num [aC]

theorem complex_log : Real.log 21952 < 10  -- json prime-field28.json witness.log_upper.complex
    := log_21952_lt_10

/-- **exponent certificate**: `s_c / W_c < 21952 ^ (1 - a_c)` -/
theorem complex_exponent :
    ((sc : ℕ) : ℝ) / (Wc : ℕ) < (21952 : ℝ) ^ (1 - (aC : ℝ)) := by
  obtain ⟨-, -, -, hW, -, -, hs, -⟩ := complex_counts
  rw [hs, hW, show ((aC : ℚ) : ℝ) = 39 / 10 ^ 9 by norm_num [aC]]
  apply exponent_certificate 21952 10 (39 / 10 ^ 9) (5 / 12693352) _
    (by norm_num) (by norm_num) log_21952_lt_10
  · norm_num
  · norm_num

/-- scalar gates `3v²(4(61022 + v) + 4v + 4) ≤ 12 W_c` (construction lines 233-235) -/
theorem complex_gates :
    Ic * (4 * (cxAdd + vc) + 4 * vc + 4) = 8702721518400 ∧  -- json prime-field28.json witness.complex.scalar_gates
    Ic * (4 * (cxAdd + vc) + 4 * vc + 4) ≤ 12 * Wc := by
  simp only [Wc, Ic, Rc, cxAdd, vc_eq]; norm_num

/-! ### Guard constants -/

def Eg : ℕ := 64 * (Wc + m + 1) ^ 3
def Bg : ℕ := sc + Eg
def C0n : ℕ :=
  1330227007428750171975003167066483053874539349448633868671027791264533942584236249186304  -- json prime-field28.json witness.guard.C0
def ζ : ℚ := 1 / 10000  -- json prime-field28.json witness.guard.zeta

theorem guard_constants :
    Eg = 580186831374453739191483276086074980416 ∧  -- json prime-field28.json witness.guard.E
    Bg = 580186831374453739191529048436710092608 ∧  -- json prime-field28.json witness.guard.B
    sc = 45772350635112192 ∧  -- json prime-field28.json witness.guard.s
    m = 21952 ∧  -- json prime-field28.json witness.guard.m
    3 ≤ m ∧ 2 ≤ sc ∧ sc < m ^ 5 ∧ sc * (8 + Eg) ≤ 9 * Bg ^ 2 ∧
    (C0n : ℚ) = max (128 * 21952 * (Bg : ℚ) ^ 2) (18 * 21952 * (Bg : ℚ) ^ 2 * (1 + 1 / ζ)) ∧
    9 * 21952 * (Bg : ℚ) ^ 2 * (1 + 1 / ζ) + 18 ≤ C0n ∧
    -- coefficient-depth enclosure of `prime_field_network.py`, `witness`
    36 * Wc ^ 3 + 4 * sc + 4 * Wc + 4 < Eg := by
  simp only [Eg, Bg, C0n, ζ, Wc, Lc, Dc, sc, Nc, Ic, m, Rc, vc_eq]
  norm_num

/-! ## C. The witness κ = 373/10¹¹ -/

def P : Params where
  τ := 399999997 / 400000000  -- json prime-field28.json witness.parameters.tau
  σ := 999999961 / 1000000000  -- json prime-field28.json witness.parameters.sigma
  ε := 4999 / 10000  -- json prime-field28.json witness.parameters.epsilon
  c := 9999 / 10000  -- json prime-field28.json witness.parameters.c
  lam := 99999999251 / 100000000000  -- json prime-field28.json witness.parameters.lam
  lamp := 24999999813 / 25000000000  -- json prime-field28.json witness.parameters.lamp
  κ := 373 / 100000000000  -- json prime-field28.json witness.parameters.kappa
  β := 19 / 25  -- json prime-field28.json witness.parameters.beta
  δ := 1 / 1000000  -- json prime-field28.json witness.parameters.delta
  C1 := 19601 / 10000  -- json prime-field28.json witness.parameters.C1

/-- the parameters of construction lines 241-250 -/
theorem parameter_origin :
    P.τ = 1 - 3 / 400000000 ∧ P.σ = 1 - 39 / 10 ^ 9 ∧ P.lam = 1 - 749 / 10 ^ 11 ∧
    P.lamp = 1 - 748 / 10 ^ 11 ∧ P.κ = 373 / 10 ^ 11 ∧ P.C1 = 5 - 4 * P.β + ζ ∧
    P.β = 19 / 25 ∧  -- json prime-field28.json witness.guard.beta
    P.C1 = 19601 / 10000 ∧  -- json prime-field28.json witness.guard.C1
    1 - P.τ = aB ∧ 1 - P.σ = aC
    := by
  norm_num [P, ζ, aB, aC]

/-- `τ` and `σ` are the exponents certified by the two networks -/
theorem exponents_certified :
    ((sb : ℕ) : ℝ) / (Wb : ℕ) < (21952 : ℝ) ^ ((P.τ : ℚ) : ℝ) ∧
    ((sc : ℕ) : ℝ) / (Wc : ℕ) < (21952 : ℝ) ^ ((P.σ : ℚ) : ℝ) := by
  have hτ : ((P.τ : ℚ) : ℝ) = 1 - (aB : ℝ) := by
    rw [show P.τ = 1 - aB by norm_num [P, aB]]; push_cast; ring
  have hσ : ((P.σ : ℚ) : ℝ) = 1 - (aC : ℝ) := by
    rw [show P.σ = 1 - aC by norm_num [P, aC]]; push_cast; ring
  rw [hτ, hσ]; exact ⟨bit_exponent, complex_exponent⟩

theorem recurrence_values :
    P.internal = 399999997 / 400000000 ∧  -- json prime-field28.json witness.recurrence.internal
    P.leaf = 12499999883 / 12500000000 ∧  -- json prime-field28.json witness.recurrence.leaf
    P.prep = 1 / 10000 ∧  -- json prime-field28.json witness.recurrence.preprocessing
    P.layer = 399999997 / 400000000  -- json prime-field28.json witness.recurrence.layer
    := by
  norm_num [P, Params.internal, Params.leaf, Params.prep, Params.layer]

theorem slack_values :
    P.ε * P.c = 49985001 / 100000000 ∧  -- json prime-field28.json witness.constraints.K_dominates_log_p
    1 - P.ε - P.ε * P.c = 24999 / 100000000 ∧  -- json prime-field28.json witness.constraints.K_smaller_than_ell
    1 - 2 * P.ε = 1 / 5000 ∧  -- json prime-field28.json witness.constraints.alpha_squared_theta_growth
    1 - P.β = 6 / 25 ∧  -- json prime-field28.json witness.constraints.beta_below_one
    P.β = 19 / 25 ∧  -- json prime-field28.json witness.constraints.beta_positive
    P.c = 9999 / 10000 ∧  -- json prime-field28.json witness.constraints.c_positive
    1 - P.τ - P.ε * (1 - P.τ) = 15003 / 4000000000000 ∧  -- json prime-field28.json witness.constraints.crt_layout
    1 / 8 - P.δ = 124999 / 1000000 ∧  -- json prime-field28.json witness.constraints.delta_below_one_eighth
    P.δ = 1 / 1000000 ∧  -- json prime-field28.json witness.constraints.delta_positive
    P.ε = 4999 / 10000 ∧  -- json prime-field28.json witness.constraints.epsilon_positive
    1 - P.δ - 2 * P.ε = 199 / 1000000 ∧  -- json prime-field28.json witness.constraints.gaussian_cost
    1 - P.ε * P.C1 = 2014601 / 100000000 ∧  -- json prime-field28.json witness.constraints.guard_width
    P.κ = 373 / 100000000000 ∧  -- json prime-field28.json witness.constraints.kappa_positive
    P.lam - P.σ = 3151 / 100000000000 ∧  -- json prime-field28.json witness.constraints.lambda_above_sigma
    P.lam - P.τ = 1 / 100000000000 ∧  -- json prime-field28.json witness.constraints.lambda_above_tau
    1 - P.lam = 749 / 100000000000 ∧  -- json prime-field28.json witness.constraints.lambda_below_one
    P.lamp - P.lam = 1 / 100000000000 ∧  -- json prime-field28.json witness.constraints.lambda_prime_above_lambda
    1 - P.lamp = 187 / 25000000000 ∧  -- json prime-field28.json witness.constraints.lambda_prime_below_one
    P.lamp - (P.σ + P.β * (1 - P.σ)) = 47 / 25000000000 ∧  -- json prime-field28.json witness.constraints.leaf_cost
    P.lam - P.internal = 1 / 100000000000 ∧  -- json prime-field28.json witness.constraints.packed_overhead
    1 - P.ε * (1 + P.c) = 24999 / 100000000 ∧  -- json prime-field28.json witness.constraints.prefix_cost
    1 - 2 * P.ε = 1 / 5000 ∧  -- json prime-field28.json witness.constraints.prime_interval_growth
    1 - P.ε = 5001 / 10000 ∧  -- json prime-field28.json witness.constraints.r_superpolynomial
    P.lamp - P.prep = 24997499813 / 25000000000 ∧  -- json prime-field28.json witness.constraints.reserved_axes
    1 - P.δ - P.ε = 500099 / 1000000 ∧  -- json prime-field28.json witness.constraints.scalar_cost
    1 - P.σ = 39 / 1000000000 ∧  -- json prime-field28.json witness.constraints.sigma_below_one
    P.σ = 999999961 / 1000000000 ∧  -- json prime-field28.json witness.constraints.sigma_positive
    1 - P.τ = 3 / 400000000 ∧  -- json prime-field28.json witness.constraints.tau_below_one
    P.τ = 399999997 / 400000000  -- json prime-field28.json witness.constraints.tau_positive
    := by
  norm_num [P, Params.internal, Params.prep]

theorem constraint_slacks :
    0 < P.ε * P.c ∧  -- K_dominates_log_p
    0 < 1 - P.ε - P.ε * P.c ∧  -- K_smaller_than_ell
    0 < 1 - 2 * P.ε ∧  -- alpha_squared_theta_growth
    0 < 1 - P.β ∧  -- beta_below_one
    0 < P.β ∧  -- beta_positive
    0 < P.c ∧  -- c_positive
    0 < 1 - P.τ - P.ε * (1 - P.τ) ∧  -- crt_layout
    0 < 1 / 8 - P.δ ∧  -- delta_below_one_eighth
    0 < P.δ ∧  -- delta_positive
    0 < P.ε ∧  -- epsilon_positive
    0 < 1 - P.δ - 2 * P.ε ∧  -- gaussian_cost
    0 < 1 - P.ε * P.C1 ∧  -- guard_width
    0 < P.κ ∧  -- kappa_positive
    0 < P.lam - P.σ ∧  -- lambda_above_sigma
    0 < P.lam - P.τ ∧  -- lambda_above_tau
    0 < 1 - P.lam ∧  -- lambda_below_one
    0 < P.lamp - P.lam ∧  -- lambda_prime_above_lambda
    0 < 1 - P.lamp ∧  -- lambda_prime_below_one
    0 < P.lamp - (P.σ + P.β * (1 - P.σ)) ∧  -- leaf_cost
    0 < P.lam - P.internal ∧  -- packed_overhead
    0 < 1 - P.ε * (1 + P.c) ∧  -- prefix_cost
    0 < 1 - 2 * P.ε ∧  -- prime_interval_growth
    0 < 1 - P.ε ∧  -- r_superpolynomial
    0 < P.lamp - P.prep ∧  -- reserved_axes
    0 < 1 - P.δ - P.ε ∧  -- scalar_cost
    0 < 1 - P.σ ∧  -- sigma_below_one
    0 < P.σ ∧  -- sigma_positive
    0 < 1 - P.τ ∧  -- tau_below_one
    0 < P.τ  -- tau_positive
    := by
  norm_num [P, Params.internal, Params.prep]

theorem margin_values :
    P.g1 = 24999 / 100000000 ∧  -- json prime-field28.json witness.margins.g1
    P.g2 = 149955003 / 40000000000000000 ∧  -- json prime-field28.json witness.margins.g2
    P.g3 = 934813 / 250000000000000 ∧  -- json prime-field28.json witness.margins.g3
    P.g4 = 15003 / 4000000000000 ∧  -- json prime-field28.json witness.margins.g4
    P.g5fast = 199 / 1000000 ∧  -- json prime-field28.json witness.margins.g5
    P.g6 = 500099 / 1000000 ∧  -- json prime-field28.json witness.margins.g6
    P.g7 = 4999 / 10000  -- json prime-field28.json witness.margins.g7
    := by
  norm_num [P, Params.g1, Params.g2, Params.g3, Params.g4, Params.g5fast, Params.g6, Params.g7]

/-- **headline**: `g3 = 934813/(25·10¹³)` is the minimum margin, `κ = 373/10¹¹` is below it
by `2313/(25·10¹³)`, and `2^-28 < κ < 2^-27` -/
theorem kappa_witness :
    P.g3 ≤ P.g1 ∧ P.g3 ≤ P.g2 ∧ P.g3 ≤ P.g4 ∧ P.g3 ≤ P.g5fast ∧ P.g3 ≤ P.g6 ∧ P.g3 ≤ P.g7 ∧
    P.g3 = 934813 / 250000000000000 ∧  -- json prime-field28.json witness.minimum_margin
    P.g3 - P.κ = 2313 / 250000000000000 ∧  -- json prime-field28.json witness.absorption_gap
    P.κ < P.g3 ∧ (1 : ℚ) / 2 ^ 28 < P.κ ∧ P.κ < 1 / 2 ^ 27 := by
  norm_num [P, Params.g1, Params.g2, Params.g3, Params.g4, Params.g5fast, Params.g6, Params.g7]

/-- further comparisons: internal exponent `= τ`, layer ordering, guard and leaf windows,
the `2^-28` margin (`κ·2^28 > 1.001`), and the bit network's own ceiling `κ < a/2` -/
theorem note_lines :
    P.σ < P.τ ∧ P.internal = P.τ ∧ max (max P.τ P.σ) P.internal < P.lam ∧ P.lam < P.lamp ∧
    P.lamp < 1 ∧ max (P.σ + P.β * (1 - P.σ)) (1 - P.c) < P.lamp ∧
    P.ε * P.C1 = 97985399 / 10 ^ 8 ∧ P.ε * P.C1 < 1 ∧
    1 - P.lamp < (1 - P.β) * (39 / 10 ^ 9) ∧
    (1001 : ℚ) / 1000 / 2 ^ 28 < P.κ ∧ P.κ < (3 : ℚ) / 400000000 / 2 := by
  norm_num [P, Params.internal]

/-- the fast-Gaussian margins with **τ fixed at `P.τ = 1 - a`** give `κ < a/2 = 3/800000000`
(not stated in the PR; the network itself certifies `1 - τ` up to about `7.502·10⁻⁹`, so this
is not a ceiling for the network) -/
theorem scoped_ceiling (ε' lamp' κ' : ℝ) (hl : ((P.τ : ℚ) : ℝ) < lamp') (hε : 0 < ε')
    (h3 : κ' < ε' * (1 - lamp')) (h4 : κ' < (1 - ((P.τ : ℚ) : ℝ)) * (1 - ε')) :
    κ' < 3 / 800000000 ∧ (3 : ℝ) / 800000000 < 1 / 2 ^ 27 := by
  have hτ : ((P.τ : ℚ) : ℝ) = 1 - 3 / 400000000 := by norm_num [P]
  rw [hτ] at hl h4
  have := ceiling_half (1 - 3 / 400000000) ε' lamp' κ' (by norm_num) hl hε h3 h4
  exact ⟨by linarith, by norm_num⟩

/-! ## D. Algebraic claims of the construction note and the `h = 8` controls -/

/-- eigenvalue `1 - 2h/25 = -31/25`, `⟨t_S,t_T⟩ = |S∩T| - 2`, `⟨t_T,t_T⟩ = 3`, the mod-3
coefficient `C(k,2) - [k=2] ≡ [k=5]` for `0 ≤ k ≤ 5`, the positive-definiteness identity
`|u|² - (2/25)(Σu)² = Σ_{i∉{a,b}} u_i²` (with `u_a = u_b = t`, `Σu = 5t`), and the join
dimensions `(h²-1)h + h = h³` -/
theorem motif_algebra :
    (1 : ℚ) - 2 * 28 / 25 = -31 / 25 ∧ (∀ k : ℚ, k - 2 / 25 * 5 * 5 = k - 2) ∧
    (5 : ℚ) - 2 / 25 * 5 * 5 = 3 ∧
    (∀ k : Fin 6, ((Nat.choose k 2 : ℤ) - if (k : ℕ) = 2 then 1 else 0) % 3 =
      if (k : ℕ) = 5 then 1 else 0) ∧
    (∀ S t : ℝ, (S + 2 * t ^ 2) - 2 / 25 * (5 * t) ^ 2 = S) ∧
    (∀ h : ℤ, (h ^ 2 - 1) * h + h = h ^ 3) ∧ 28 / 2 - 1 - 1 = 12 := by
  refine ⟨by norm_num, fun k => by ring, by norm_num, by decide, fun S t => by ring,
    fun h => by ring, by norm_num⟩

def v8 : ℕ := 56  -- json prime-field28.json small_controls.coefficients.inputs
/-- roles of the `h = 8` producer: **taken as given** -/
def R8 : ℕ := 1044  -- json prime-field28.json small_controls.coefficients.roles

/-- `h = 8`: `v = C(8,5)`, loss `C(8,2)·6`, total rank `(2v+R)h - 2v + 2·loss`, basis
inputs `2v + R` (the asserts of `frame_control` and `scalar_control`) -/
theorem small_controls :
    v8 = Nat.choose 8 5 ∧
    Nat.choose 8 2 * 6 = 168 ∧  -- json prime-field28.json small_controls.physical_frames.frames.0.loss
    (2 * v8 + R8) * 8 - 2 * v8 + 2 * 168 = 9472 ∧  -- json prime-field28.json small_controls.physical_frames.frames.0.total_rank
    2 * v8 + R8 = 1156  -- json prime-field28.json small_controls.all_dirty_basis.all_basis_inputs
    := by
  refine ⟨by decide, by decide, by norm_num [v8, R8], by norm_num [v8, R8]⟩

end PRChecksB.PR7
