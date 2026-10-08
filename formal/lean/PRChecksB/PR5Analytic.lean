import PRChecksB.Common
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# PR #5: the rational and real inequalities of the new resampling lemmas

Sources (worktree `/home/user/prs/pr5`): `notes/fast-gaussian-resampling.tex`
(Lemma `lem:correction-powers`, Corollary `cor:neumann-count`, Lemma
`lem:chirped-gaussian`), `notes/fast-gaussian-note.tex` (Lemma
`lem:no-sort-resampling`, "Gaussian width"), `patches/fast-gaussian-30.patch`, and
`scripts/fast_gaussian.py` (`neumann_count`, `application_counts`, `KAPPA0_LO/HI`).

Only the scalar arithmetic is checked: identities, the potential and path bounds,
the inner Gaussian series bound, the Neumann count from the power bound, the Gaussian
width consequences, the chirp-lemma constants, and the three certified Neumann samples.
The operator-norm statements themselves (`‖E^n‖ ≤ …`, the cited Lemmas 4.6–4.12) and
the algorithms are not formalized.
-/

namespace PRChecksB.PR5Analytic

open Real

/-! ## Chirp identity (`lem:chirped-gaussian`, eq. `chirp-split`) -/

theorem chirp_square (σ θ a b : ℝ) (hσ : σ = 1 + θ) :
    (σ * a - b) ^ 2 = σ * θ * a ^ 2 + σ * (a - b) ^ 2 - θ * b ^ 2 := by
  subst hσ; ring

/-- `e^{-πλ(σa+y-b)²} = e^{πλθb²} e^{-πλσθ(a+y/σ)²} e^{-πλσ(a-b+y/σ)²}` -/
theorem chirp_split (σ θ lam a b y : ℝ) (hσ : σ = 1 + θ) (hσ0 : σ ≠ 0) :
    Real.exp (-π * lam * (σ * a + y - b) ^ 2) =
      Real.exp (π * lam * θ * b ^ 2) * Real.exp (-π * lam * σ * θ * (a + y / σ) ^ 2) *
        Real.exp (-π * lam * σ * (a - b + y / σ) ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have key := chirp_square σ θ (a + y / σ) b hσ
  have e1 : σ * (a + y / σ) = σ * a + y := by field_simp; ring
  have e2 : a + y / σ - b = a - b + y / σ := by ring
  rw [e1, e2] at key
  rw [key]; ring

/-! ## The step inequality (`lem:correction-powers`) -/

/-- `c(j,h) = (σh + β_j)² - β_j² = σh(σh + 2β_j)` -/
theorem step_cost (σ h βj : ℝ) : (σ * h + βj) ^ 2 - βj ^ 2 = σ * h * (σ * h + 2 * βj) := by
  ring

/-- `β_{j+h} = β_j + σh - (q_{j+h} - q_j) = y - w` with `y = β_j + hθ`, `w = q_{j+h}-q_j-h` -/
theorem step_phase (σ θ h βj qj qjh : ℝ) (hσ : σ = 1 + θ) :
    βj + σ * h - (qjh - qj) = (βj + h * θ) - (qjh - qj - h) := by
  subst hσ; ring

/-- the closed form `c(j,h) - Φ(j+h) + Φ(j) = σh² + (σ/θ) w (2y - w)`, with
`Φ = σ(β² + 1/4)/θ`, `β_j = y - hθ`, `β_{j+h} = y - w` (also checked by the script's
`step_inequality` on five `(s,t)`) -/
theorem step_identity (σ θ h y w : ℝ) (hσ : σ = 1 + θ) (hθ : θ ≠ 0) :
    σ * h * (σ * h + 2 * (y - h * θ)) - σ * ((y - w) ^ 2 + 1 / 4) / θ +
        σ * ((y - h * θ) ^ 2 + 1 / 4) / θ =
      σ * h ^ 2 + σ / θ * w * (2 * y - w) := by
  subst hσ; field_simp; ring

/-- `w(2y - w) ≥ 0` for an integer `w` with `|y - w| ≤ 1/2` -/
theorem step_nonneg (w : ℤ) (y : ℝ) (hy : |y - w| ≤ 1 / 2) : 0 ≤ (w : ℝ) * (2 * y - w) := by
  rcases eq_or_ne w 0 with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ |(w : ℝ)| := by
      have : (1 : ℤ) ≤ |w| := Int.one_le_abs h
      exact_mod_cast this
    have h2 : |(w : ℝ)| ≤ (w : ℝ) ^ 2 := by
      rw [← sq_abs]; nlinarith
    have h3 : |(w : ℝ) * (y - w)| ≤ |(w : ℝ)| * (1 / 2) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    have h4 := neg_abs_le ((w : ℝ) * (y - w))
    nlinarith

/-- `σ/(4θ) ≤ Φ ≤ σ/(2θ)` when `β² ≤ 1/4` -/
theorem potential_bounds (σ θ b : ℝ) (hθ : 0 < θ) (hσ : 0 ≤ σ) (hb : b ^ 2 ≤ 1 / 4) :
    σ / (4 * θ) ≤ σ * (b ^ 2 + 1 / 4) / θ ∧ σ * (b ^ 2 + 1 / 4) / θ ≤ σ / (2 * θ) := by
  have hσθ : 0 ≤ σ * θ := mul_nonneg hσ hθ.le
  constructor
  · rw [div_le_div_iff₀ (by positivity) hθ]
    nlinarith [mul_nonneg hσθ (sq_nonneg b)]
  · rw [div_le_div_iff₀ hθ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hb hσθ]

/-- `σ/(4θ) + 1/4 = 1/(4θ) + 1/2` -/
theorem path_constant (σ θ : ℝ) (hσ : σ = 1 + θ) (hθ : θ ≠ 0) :
    σ / (4 * θ) + 1 / 4 = 1 / (4 * θ) + 1 / 2 := by
  subst hσ; field_simp; ring

/-- summing the step inequality along a path:
`X = Σ c + β_{j_0}² - β_{j_n}² ≥ σ Σ h² - 1/(4θ) - 1/2` -/
theorem path_bound (σ θ : ℝ) (hθ : 0 < θ) (hσ : σ = 1 + θ) (n : ℕ) (h c β : ℕ → ℝ)
    (hβ : ∀ i, β i ^ 2 ≤ 1 / 4)
    (hstep : ∀ i < n, σ * h i ^ 2 ≤
      c i - σ * (β (i + 1) ^ 2 + 1 / 4) / θ + σ * (β i ^ 2 + 1 / 4) / θ) :
    σ * ∑ i ∈ Finset.range n, h i ^ 2 - 1 / (4 * θ) - 1 / 2 ≤
      ∑ i ∈ Finset.range n, c i + β 0 ^ 2 - β n ^ 2 := by
  have tele := Finset.sum_range_sub (fun i => σ * (β i ^ 2 + 1 / 4) / θ) n
  simp only at tele
  have hle : ∑ i ∈ Finset.range n, σ * h i ^ 2 ≤
      ∑ i ∈ Finset.range n, (c i - (σ * (β (i + 1) ^ 2 + 1 / 4) / θ -
        σ * (β i ^ 2 + 1 / 4) / θ)) :=
    Finset.sum_le_sum (fun i hi => by have := hstep i (Finset.mem_range.mp hi); linarith)
  rw [Finset.sum_sub_distrib, tele, ← Finset.mul_sum] at hle
  have hσ0 : 0 ≤ σ := by linarith
  have b0 := potential_bounds σ θ (β 0) hθ hσ0 (hβ 0)
  have bn := potential_bounds σ θ (β n) hθ hσ0 (hβ n)
  have hc := path_constant σ θ hσ hθ.ne'
  have h2 : σ / (2 * θ) = 2 * (σ / (4 * θ)) := by field_simp; ring
  have hb0 := sq_nonneg (β 0)
  have hbn := hβ n
  linarith [b0.2, bn.1]

/-- the inner Gaussian series: for `x = πα²σ ≥ 4π`,
`Σ_{h≥1} e^{-xh²} ≤ e^{-x}(1 + 2e^{-3x})` (the sum over `h ≠ 0` is twice this) -/
theorem inner_sum_bound (x : ℝ) (hx : 4 * π ≤ x) :
    ∑' k : ℕ, Real.exp (-(x * ((k : ℝ) + 1) ^ 2)) ≤
      Real.exp (-x) * (1 + 2 * Real.exp (-(3 * x))) := by
  have hpi := Real.pi_gt_three
  have hx0 : 0 < x := by linarith
  set r := Real.exp (-(5 * x)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 / 2 := by
    have h1 : 1 + 5 * x ≤ Real.exp (5 * x) := by linarith [Real.add_one_le_exp (5 * x)]
    have hprod : r * Real.exp (5 * x) = 1 := by rw [hr, ← Real.exp_add]; simp
    nlinarith
  have hg : ∀ k : ℕ, Real.exp (-(x * ((k : ℝ) + 2) ^ 2)) ≤ Real.exp (-(4 * x)) * r ^ k := by
    intro k
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h
        nlinarith
    nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hk)]
  have hsumg : Summable (fun k : ℕ => Real.exp (-(4 * x)) * r ^ k) :=
    (summable_geometric_of_lt_one hr0 (by linarith)).mul_left _
  have hsum2 : Summable (fun k : ℕ => Real.exp (-(x * ((k : ℝ) + 2) ^ 2))) :=
    Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) hg hsumg
  have hshift : (fun k : ℕ => Real.exp (-(x * (((k + 1 : ℕ) : ℝ) + 1) ^ 2))) =
      (fun k : ℕ => Real.exp (-(x * ((k : ℝ) + 2) ^ 2))) := by
    funext k; push_cast; ring_nf
  have hsum1 : Summable (fun k : ℕ => Real.exp (-(x * ((k : ℝ) + 1) ^ 2))) := by
    rw [← summable_nat_add_iff 1]
    exact hshift ▸ hsum2
  rw [hsum1.tsum_eq_zero_add, hshift]
  have htail : ∑' k : ℕ, Real.exp (-(x * ((k : ℝ) + 2) ^ 2)) ≤ Real.exp (-(4 * x)) * (1 - r)⁻¹ := by
    calc ∑' k : ℕ, Real.exp (-(x * ((k : ℝ) + 2) ^ 2))
        ≤ ∑' k : ℕ, Real.exp (-(4 * x)) * r ^ k := Summable.tsum_le_tsum hg hsum2 hsumg
      _ = Real.exp (-(4 * x)) * (1 - r)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h4 : Real.exp (-(4 * x)) = Real.exp (-x) * Real.exp (-(3 * x)) := by
    rw [← Real.exp_add]; ring_nf
  have he4 : 0 < Real.exp (-(4 * x)) := Real.exp_pos _
  have htail2 : Real.exp (-(4 * x)) * (1 - r)⁻¹ ≤ Real.exp (-(4 * x)) * 2 :=
    mul_le_mul_of_nonneg_left hinv he4.le
  simp only [Nat.cast_zero, zero_add, one_pow, mul_one]
  rw [h4] at htail2
  nlinarith

/-- and `2(1 + 2e^{-3x}) < 2.01` for `x ≥ 4π` -/
theorem inner_sum_constant (x : ℝ) (hx : 4 * π ≤ x) :
    2 * (1 + 2 * Real.exp (-(3 * x))) < 201 / 100 := by
  have hpi := Real.pi_gt_three
  have hx12 : 12 < x := by linarith
  have e1 : 13 < Real.exp x := by linarith [Real.add_one_le_exp x]
  have e3 : Real.exp (3 * x) = Real.exp x ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have e3b : (400 : ℝ) < Real.exp (3 * x) := by
    rw [e3]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13) e1.le 3]
  have hpos := Real.exp_pos (-(3 * x))
  have hprod : Real.exp (-(3 * x)) * Real.exp (3 * x) = 1 := by
    rw [← Real.exp_add]; simp
  have : Real.exp (-(3 * x)) * 400 < Real.exp (-(3 * x)) * Real.exp (3 * x) :=
    mul_lt_mul_of_pos_left e3b hpos
  linarith

/-! ## The Neumann count (`cor:neumann-count`) -/

/-- `4.531 < κ₀ = π log₂ e = π / log 2 < 4.534` -/
theorem kappa0_bounds : (4531 / 1000 : ℝ) < π / Real.log 2 ∧ π / Real.log 2 < 4534 / 1000 := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  norm_num at hl1 hl2 hp1 hp2
  have hl0 : 0 < Real.log 2 := by linarith
  constructor
  · rw [lt_div_iff₀ hl0]; linarith
  · rw [div_lt_iff₀ hl0]; linarith

/-- `log₂ 2.01 < 1.01`, from `2.01^100 < 2^101` -/
theorem log_201 : Real.log (201 / 100) < 101 / 100 * Real.log 2 := by
  have h : ((201 : ℝ) / 100) ^ 100 < 2 ^ 101 := by norm_num
  have h1 : Real.log (((201 : ℝ) / 100) ^ 100) < Real.log (2 ^ 101) :=
    Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  push_cast at h1
  linarith

/-- the corollary's exponent arithmetic, with `A = α²`: if `α² ≥ 4`, `0 < θ < 1`,
`σ ≥ 1` and `n ≥ (p+1)/(4α²) + 1/θ`, then
`πα²(1/(4θ) + 1/2) - n(πα²σ - log 2.01) ≤ -(p+1) log 2` -/
theorem neumann_log (A θ σ p n : ℝ) (hA : 4 ≤ A) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hσ : 1 ≤ σ)
    (hp : 0 ≤ p) (hn : (p + 1) / (4 * A) + 1 / θ ≤ n) :
    π * A * (1 / (4 * θ) + 1 / 2) - n * (π * A * σ - Real.log (201 / 100)) ≤
      -(p + 1) * Real.log 2 := by
  obtain ⟨k1, k2⟩ := kappa0_bounds
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hπ1 : 4531 / 1000 * Real.log 2 < π := by rwa [lt_div_iff₀ hl0] at k1
  have hπ2 : π < 4534 / 1000 * Real.log 2 := by rwa [div_lt_iff₀ hl0] at k2
  have h201 := log_201
  have hA0 : 0 < A := by linarith
  have ht1 : 1 < 1 / θ := by rw [lt_div_iff₀ hθ0]; linarith
  have h4θ : 1 / (4 * θ) = (1 / θ) / 4 := by field_simp; ring
  rw [h4θ]
  set t := 1 / θ with ht
  have hn' : p + 1 + 4 * A * t ≤ 4 * A * n := by
    have h := mul_le_mul_of_nonneg_left hn (by linarith : (0 : ℝ) ≤ 4 * A)
    rw [mul_add, mul_div_cancel₀ _ (by positivity)] at h
    linarith
  have hn0 : 0 ≤ n := by
    have : 0 ≤ (p + 1) / (4 * A) := by positivity
    linarith
  have a1 : π * A * (t / 4 + 1 / 2) ≤ 4 * Real.log 2 * A * t := by
    have m1 : π * (t / 4 + 1 / 2) ≤ 4534 / 1000 * Real.log 2 * (t / 4 + 1 / 2) :=
      mul_le_mul_of_nonneg_right hπ2.le (by positivity)
    have m2 : 4534 / 1000 * Real.log 2 * (t / 4 + 1 / 2) ≤ 4 * Real.log 2 * t := by
      nlinarith [mul_pos hl0 (by linarith : (0 : ℝ) < 28665 / 10000 * t - 2267 / 1000)]
    calc π * A * (t / 4 + 1 / 2) = A * (π * (t / 4 + 1 / 2)) := by ring
      _ ≤ A * (4 * Real.log 2 * t) := mul_le_mul_of_nonneg_left (by linarith) hA0.le
      _ = 4 * Real.log 2 * A * t := by ring
  have a2 : 4 * Real.log 2 * A ≤ π * A * σ - Real.log (201 / 100) := by
    have m1 : π * A ≤ π * A * σ := le_mul_of_one_le_right (by positivity) hσ
    have m2 : 4531 / 1000 * Real.log 2 * A ≤ π * A :=
      mul_le_mul_of_nonneg_right hπ1.le hA0.le
    have m3 : (4 * A + 101 / 100) * Real.log 2 ≤ 4531 / 1000 * Real.log 2 * A := by
      nlinarith [mul_nonneg hl0.le (by linarith : (0 : ℝ) ≤ 531 / 1000 * A - 101 / 100)]
    nlinarith
  have a3 : n * (4 * Real.log 2 * A) ≤ n * (π * A * σ - Real.log (201 / 100)) :=
    mul_le_mul_of_nonneg_left a2 hn0
  have a4 : Real.log 2 * (p + 1 + 4 * A * t) ≤ Real.log 2 * (4 * A * n) :=
    mul_le_mul_of_nonneg_left hn' hl0.le
  nlinarith

/-- **Corollary `cor:neumann-count`, arithmetic part**: the power bound of
`lem:correction-powers` at `n ≥ (p+1)/(4α²) + 1/θ` is at most `2^{-(p+1)}` -/
theorem neumann_power (A θ σ p : ℝ) (n : ℕ) (hA : 4 ≤ A) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hσ : 1 ≤ σ) (hp : 0 ≤ p) (hn : (p + 1) / (4 * A) + 1 / θ ≤ n) :
    Real.exp (π * A * (1 / (4 * θ) + 1 / 2)) * (201 / 100 * Real.exp (-(π * A * σ))) ^ n ≤
      (2 : ℝ) ^ (-(p + 1)) := by
  have hl := neumann_log A θ σ p n hA hθ0 hθ1 hσ hp hn
  rw [Real.rpow_def_of_pos (by norm_num)]
  rw [show (201 / 100 : ℝ) = Real.exp (Real.log (201 / 100)) from
    (Real.exp_log (by norm_num)).symm]
  rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- if `α²θ ≥ 1` then `p/(α²θ) ≤ p`, so `⌈p/(α²θ)⌉ ≤ p` -/
theorem neumann_le_p (p A θ : ℝ) (hp : 0 ≤ p) (h : 1 ≤ A * θ) : p / (A * θ) ≤ p :=
  div_le_self hp h

/-! ## The script's constants (`scripts/fast_gaussian.py`) -/

def K0LO : ℚ := (333 / 106) / (6932 / 10000)
def K0HI : ℚ := (355 / 113) / (693 / 1000)

/-- `333/106 < π < 355/113`, `0.693 < log 2 < 0.6932`, hence
`KAPPA0_LO < π/log 2 < KAPPA0_HI` -/
theorem script_kappa0 :
    (333 / 106 : ℝ) < π ∧ π < 355 / 113 ∧ (693 / 1000 : ℝ) < Real.log 2 ∧
    Real.log 2 < 6932 / 10000 ∧ (K0LO : ℝ) < π / Real.log 2 ∧ π / Real.log 2 < (K0HI : ℝ) := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d20
  norm_num at hl1 hl2 hp1 hp2
  have hl0 : 0 < Real.log 2 := by linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [lt_div_iff₀ hl0]; unfold K0LO; push_cast; nlinarith
  · rw [div_lt_iff₀ hl0]; unfold K0HI; push_cast; nlinarith

/-- `2.01^100 < 2^101` and `KAPPA0_LO α² - 101/100 ≥ 4α²` for every `α ≥ 2` -/
theorem script_step (A : ℚ) (hA : 4 ≤ A) :
    ((201 : ℚ) / 100) ^ 100 < 2 ^ 101 ∧ 4 * A ≤ K0LO * A - 101 / 100 := by
  refine ⟨by norm_num, ?_⟩
  unfold K0LO; nlinarith

/-! ## The three certified Neumann samples (`fast-gaussian.json`, `neumann_samples`) -/

/-- `α = ⌊√(b/(8d))⌋`, `γ = 2dα²`, `θ = 1/(4d)`, `n_new = ⌈(6b+1)/(4α²) + 1/θ⌉`,
`n_hvdh = ⌈6b/(α²θ)⌉`, `n = min`, and the script's checks (including `θ < 1`) -/
def SampleOK (d b α γ nNew nH n : ℕ) : Prop :=
  8 * d * α ^ 2 ≤ b ∧ b < 8 * d * (α + 1) ^ 2 ∧ γ = 2 * d * α ^ 2 ∧ 4 * γ ≤ b ∧
  ((nNew : ℚ) - 1 < (6 * b + 1) / (4 * α ^ 2) + 4 * d) ∧
  ((6 * b + 1 : ℚ) / (4 * α ^ 2) + 4 * d ≤ nNew) ∧
  ((nH : ℚ) - 1 < 6 * b * (4 * d) / α ^ 2) ∧ ((6 * b : ℚ) * (4 * d) / α ^ 2 ≤ nH) ∧
  n = min nNew nH ∧ nNew ≤ 30 * d ∧ 2 ≤ α ∧ (1 : ℚ) ≤ α ^ 2 / (4 * d) ∧ (1 : ℚ) / (4 * d) < 1 ∧
  (6 * b + 1 : ℚ) + K0HI * α ^ 2 * (d + 1 / 2) ≤ 4 * α ^ 2 * nNew ∧
  4 * (α : ℚ) ^ 2 ≤ K0LO * α ^ 2 - 101 / 100

def s0d : ℕ := 8  -- json fast-gaussian.json neumann_samples.0.d
def s0b : ℕ := 1048576  -- json fast-gaussian.json neumann_samples.0.b
def s0α : ℕ := 128  -- json fast-gaussian.json neumann_samples.0.alpha
def s0γ : ℕ := 262144  -- json fast-gaussian.json neumann_samples.0.gamma
def s0new : ℕ := 129  -- json fast-gaussian.json neumann_samples.0.n_new
def s0h : ℕ := 12288  -- json fast-gaussian.json neumann_samples.0.n_hvdh
def s0n : ℕ := 129  -- json fast-gaussian.json neumann_samples.0.n

def s1d : ℕ := 64  -- json fast-gaussian.json neumann_samples.1.d
def s1b : ℕ := 1073741824  -- json fast-gaussian.json neumann_samples.1.b
def s1α : ℕ := 1448  -- json fast-gaussian.json neumann_samples.1.alpha
def s1γ : ℕ := 268378112  -- json fast-gaussian.json neumann_samples.1.gamma
def s1new : ℕ := 1025  -- json fast-gaussian.json neumann_samples.1.n_new
def s1h : ℕ := 786601  -- json fast-gaussian.json neumann_samples.1.n_hvdh
def s1n : ℕ := 1025  -- json fast-gaussian.json neumann_samples.1.n

def s2d : ℕ := 1000  -- json fast-gaussian.json neumann_samples.2.d
def s2b : ℕ := 1099511627776  -- json fast-gaussian.json neumann_samples.2.b
def s2α : ℕ := 11723  -- json fast-gaussian.json neumann_samples.2.alpha
def s2γ : ℕ := 274857458000  -- json fast-gaussian.json neumann_samples.2.gamma
def s2new : ℕ := 16001  -- json fast-gaussian.json neumann_samples.2.n_new
def s2h : ℕ := 192014285  -- json fast-gaussian.json neumann_samples.2.n_hvdh
def s2n : ℕ := 16001  -- json fast-gaussian.json neumann_samples.2.n

theorem sample0 : SampleOK s0d s0b s0α s0γ s0new s0h s0n := by
  unfold SampleOK K0LO K0HI s0d s0b s0α s0γ s0new s0h s0n; norm_num

theorem sample1 : SampleOK s1d s1b s1α s1γ s1new s1h s1n := by
  unfold SampleOK K0LO K0HI s1d s1b s1α s1γ s1new s1h s1n; norm_num

theorem sample2 : SampleOK s2d s2b s2α s2γ s2new s2h s2n := by
  unfold SampleOK K0LO K0HI s2d s2b s2α s2γ s2new s2h s2n; norm_num

/-! ## Gaussian width (`fast-gaussian-note.tex` 109-122, patch lines 175-203) -/

/-- with `α = ⌊√(b/(8d))⌋` (i.e. `8dα² ≤ b < 8d(α+1)²`) and `b ≥ 96d`:
`√(b/(8d)) ≥ 2√3`, `α ≥ 3 ≥ 2`, `α² ≥ b/(16d)`, `α² < p = 6b`, `γ = 2dα² ≤ b/4` -/
theorem gaussian_width (d b : ℝ) (α : ℕ) (hd : 1 ≤ d) (hb : 96 * d ≤ b)
    (hlo : 8 * d * (α : ℝ) ^ 2 ≤ b) (hhi : b < 8 * d * ((α : ℝ) + 1) ^ 2) :
    12 ≤ b / (8 * d) ∧ 3 ≤ α ∧ b / (16 * d) ≤ (α : ℝ) ^ 2 ∧ (α : ℝ) ^ 2 < 6 * b ∧
    2 * d * (α : ℝ) ^ 2 ≤ b / 4 := by
  have hd0 : 0 < d := by linarith
  have hα0 : (0 : ℝ) ≤ α := Nat.cast_nonneg α
  have h12 : (12 : ℝ) < ((α : ℝ) + 1) ^ 2 := by nlinarith
  have hα3 : 3 ≤ α := by
    by_contra h
    push_neg at h
    have : (α : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp h
    nlinarith
  have hα3' : (3 : ℝ) ≤ α := by exact_mod_cast hα3
  refine ⟨?_, hα3, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; linarith
  · rw [div_le_iff₀ (by positivity)]
    have hsq : ((α : ℝ) + 1) ^ 2 ≤ 2 * (α : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 8 * d)]
  · nlinarith [sq_nonneg (α : ℝ)]
  · linarith

/-- `n_{α,θ} ≤ (p+1)/(4α²) + 1/θ + 1 ≤ (6b+1)16d/(4b) + 4d + 1 ≤ 30d` -/
theorem neumann_le_30d (d b A θ : ℝ) (hd : 1 ≤ d) (hb : 96 * d ≤ b) (hA : b / (16 * d) ≤ A)
    (hθ : 1 / (4 * d) < θ) : (6 * b + 1) / (4 * A) + 1 / θ + 1 ≤ 30 * d := by
  have hd0 : 0 < d := by linarith
  have hb0 : 0 < b := by linarith
  have hA' : b ≤ A * (16 * d) := by rwa [div_le_iff₀ (by positivity)] at hA
  have hA6 : 6 ≤ A := by nlinarith
  have hθ0 : 0 < θ := lt_trans (by positivity) hθ
  have h1 : 1 / θ < 4 * d := by
    rw [div_lt_iff₀ (by positivity)] at hθ
    rw [div_lt_iff₀ hθ0]; linarith
  have h2 : (6 * b + 1) / (4 * A) ≤ 24 * d + 1 / 24 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- `θ_i < 2η/(1-2η) = 1/(2d-1) ≤ 1/4` once `d ≥ 3` (patch line 161) -/
theorem theta_window (d : ℝ) (hd : 3 ≤ d) :
    2 * (1 / (4 * d)) / (1 - 2 * (1 / (4 * d))) = 1 / (2 * d - 1) ∧ 1 / (2 * d - 1) ≤ 1 / 4 := by
  have hd0 : d ≠ 0 := by positivity
  have h1 : 2 * d - 1 ≠ 0 := by linarith
  have h2 : 4 * d - 2 ≠ 0 := by linarith
  constructor
  · field_simp; ring
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith

/-- `α²θ_i > b/(64d²) ≥ 1` once `b ≥ 64d²` -/
theorem alpha_theta (d b A θ : ℝ) (hd : 0 < d) (hA : b / (16 * d) ≤ A) (hθ : 1 / (4 * d) < θ)
    (hb : 64 * d ^ 2 ≤ b) : b / (64 * d ^ 2) < A * θ ∧ 1 ≤ b / (64 * d ^ 2) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  constructor
  · calc b / (64 * d ^ 2) = b / (16 * d) * (1 / (4 * d)) := by ring
      _ ≤ A * (1 / (4 * d)) := mul_le_mul_of_nonneg_right hA (by positivity)
      _ < A * θ := mul_lt_mul_of_pos_left hθ hA0
  · rw [le_div_iff₀ (by positivity)]; linarith

/-! ## Constants of `lem:no-sort-resampling` (cited Lemma 4.6 under `α²θ ≥ 1`) -/

theorem exp_half_pi : (479 / 100 : ℝ) < Real.exp (π / 2) := by
  have he := Real.exp_one_gt_d9
  have hpi := Real.pi_gt_d4
  norm_num at he hpi
  have hh : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hh0 := Real.exp_pos (1 / 2)
  have hhalf : (16487212 / 10000000 : ℝ) < Real.exp (1 / 2) := by nlinarith
  have hsmall : 1 + (π / 2 - 3 / 2) ≤ Real.exp (π / 2 - 3 / 2) := by
    linarith [Real.add_one_le_exp (π / 2 - 3 / 2)]
  have hsplit : Real.exp (π / 2) = Real.exp 1 * Real.exp (1 / 2) * Real.exp (π / 2 - 3 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hsplit]
  have a : (27182818283 / 10000000000 : ℝ) * (16487212 / 10000000) < Real.exp 1 * Real.exp (1 / 2) :=
    mul_lt_mul'' he hhalf (by norm_num) (by norm_num)
  have b : (107075 / 100000 : ℝ) ≤ Real.exp (π / 2 - 3 / 2) := by linarith
  have c : (27182818283 / 10000000000 : ℝ) * (16487212 / 10000000) * (107075 / 100000) ≤
      Real.exp 1 * Real.exp (1 / 2) * Real.exp (π / 2 - 3 / 2) :=
    mul_le_mul a.le b (by norm_num) (by positivity)
  have d : (479 / 100 : ℝ) < (27182818283 / 10000000000) * (16487212 / 10000000) * (107075 / 100000) := by
    norm_num
  linarith

/-- `‖N - I‖ < 2.01 e^{-πα²θ/2} ≤ 2.01 e^{-π/2} < 0.42` when `α²θ ≥ 1` (note line 86) -/
theorem lemma46_constant : (201 / 100 : ℝ) * Real.exp (-(π / 2)) < 42 / 100 := by
  have h := exp_half_pi
  have hprod : Real.exp (-(π / 2)) * Real.exp (π / 2) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-(π / 2))
  nlinarith

/-- `2.01 e^{-πx/2} < 2^{-x}` for `x = α²θ ≥ 1` (note eq. `gaussian-public-facts`) -/
theorem lemma46_dyadic (x : ℝ) (hx : 1 ≤ x) :
    (201 / 100 : ℝ) * Real.exp (-(π * x / 2)) < (2 : ℝ) ^ (-x) := by
  have h := exp_half_pi
  have hl2 := Real.log_two_lt_d9
  norm_num at hl2
  have hgap : 0 < π / 2 - Real.log 2 := by linarith [Real.pi_gt_three]
  have h1 : Real.exp (π / 2 - Real.log 2) ≤ Real.exp (x * (π / 2 - Real.log 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (π / 2 - Real.log 2) = Real.exp (π / 2) / 2 := by
    rw [Real.exp_sub, Real.exp_log two_pos]
  have h3 : (201 / 100 : ℝ) < Real.exp (x * (π / 2 - Real.log 2)) := by linarith
  rw [Real.rpow_def_of_pos two_pos]
  calc (201 / 100 : ℝ) * Real.exp (-(π * x / 2))
      < Real.exp (x * (π / 2 - Real.log 2)) * Real.exp (-(π * x / 2)) :=
        mul_lt_mul_of_pos_right h3 (Real.exp_pos _)
    _ = Real.exp (Real.log 2 * -x) := by rw [← Real.exp_add]; congr 1; ring

/-- `‖J'‖ = ‖N^{-1}‖/2 ≤ 1/(2(1 - 0.42)) < 7/8` and `‖E‖ < 1/2` -/
theorem neumann_norms : (1 : ℚ) / (2 * (1 - 42 / 100)) < 7 / 8 ∧ (42 : ℚ) / 100 < 1 / 2 := by
  norm_num

/-! ## Constants of `lem:chirped-gaussian` -/

/-- `(√p + 1)² ≤ 1.21 p` for `p ≥ 100` -/
theorem sqrt_window (p : ℝ) (hp : 100 ≤ p) : (√p + 1) ^ 2 ≤ 121 / 100 * p := by
  have hs : 10 ≤ √p := by
    rw [show (10 : ℝ) = √100 by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hp
  have hsq : √p ^ 2 = p := Real.sq_sqrt (by linarith)
  nlinarith [sq_nonneg (√p - 10)]

/-- `e^{(π/4)(1.21p)} ≤ 2^{1.4p}`, i.e. `(π/4)·1.21 < 1.4 log 2`: `Γ = ⌈1.4p⌉` suffices -/
theorem gamma_S_constant : π / 4 * (121 / 100) < 14 / 10 * Real.log 2 := by
  have := Real.pi_lt_d2; have := Real.log_two_gt_d9; norm_num at *; linarith

/-- `F = e^{πα²/4} < 2^{1.14α²}`, i.e. `π/4 < 1.14 log 2` -/
theorem F_constant : π / 4 < 114 / 100 * Real.log 2 := by
  have := Real.pi_lt_d2; have := Real.log_two_gt_d9; norm_num at *; linarith

/-- `(√p + 4α)² < 25p` when `0 ≤ α < √p` -/
theorem window_E (p α : ℝ) (hp : 0 < p) (hα0 : 0 ≤ α) (hα : α < √p) : (√p + 4 * α) ^ 2 < 25 * p := by
  have hsq : √p ^ 2 = p := Real.sq_sqrt hp.le
  have hs0 := Real.sqrt_nonneg p
  nlinarith

/-- `α(2m+2) ≤ √p + 4α` for `m ≤ √p/(2α) + 1` -/
theorem window_E_length (p α m : ℝ) (hα : 0 < α) (hm : m ≤ √p / (2 * α) + 1) :
    α * (2 * m + 2) ≤ √p + 4 * α := by
  have h := mul_le_mul_of_nonneg_left hm hα.le
  have e : α * (√p / (2 * α) + 1) = √p / 2 + α := by field_simp; ring
  rw [e] at h
  linarith

/-- `e^{(25π/4)p} ≤ 2^{29p}`, i.e. `25π/4 < 29 log 2`: `Γ = ⌈29p⌉` suffices -/
theorem gamma_E_constant : 25 * π / 4 < 29 * Real.log 2 := by
  have := Real.pi_lt_d2; have := Real.log_two_gt_d9; norm_num at *; linarith

/-- error and norm budgets: `1 + 1/4 + 1 < 3`; `3 + 1 + 1 < p/3` for `p > 15`;
`‖S'‖ + 3·2^{-p} < 3/4 + 3/16 < 1` and `‖E‖ + 5·2^{-p} < 0.42 + 5/16 < 1` for `p ≥ 4` -/
theorem error_budgets (p : ℕ) (hp : 15 < p) :
    (1 : ℚ) + 1 / 4 + 1 < 3 ∧ (3 + 1 + 1 : ℚ) < p / 3 ∧
    (3 : ℚ) / 4 + 3 / 2 ^ p < 1 ∧ (42 : ℚ) / 100 + 5 / 2 ^ p < 1 := by
  have hp' : (15 : ℚ) < p := by exact_mod_cast hp
  have h2 : (16 : ℚ) ≤ 2 ^ p := by
    have : (2 : ℚ) ^ 4 ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; exact this
  refine ⟨by norm_num, by linarith, ?_, ?_⟩
  · have : (3 : ℚ) / 2 ^ p ≤ 3 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  · have : (5 : ℚ) / 2 ^ p ≤ 5 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith

/-- precision budget for `S'` (my reconstruction of "Take P = 3p"): with
`m = ⌈√p⌉α`, `α < √p`, `L_A = 3m+3 ≤ 7p` and `log₂ L_A ≤ 0.6p - 13` for `p ≥ 100`, so
`p + ⌈1.4p⌉ + ⌈log₂ L_A⌉ + 11 ≤ 3p` (last conjunct, with `⌈x⌉ ≤ x + 1`) -/
theorem budget_S (p c α : ℝ) (hp : 100 ≤ p) (hc0 : 0 ≤ c) (hc : c ≤ √p + 1) (hα0 : 0 ≤ α)
    (hα : α ≤ √p) : 3 * (c * α) + 3 ≤ 7 * p ∧
    Real.logb 2 (3 * (c * α) + 3) ≤ 6 / 10 * p - 13 ∧
    p + (14 / 10 * p + 1) + ((6 / 10 * p - 13) + 1) + 11 ≤ 3 * p := by
  have hsq : √p ^ 2 = p := Real.sq_sqrt (by linarith)
  have hs0 := Real.sqrt_nonneg p
  have hs10 : 10 ≤ √p := by nlinarith
  have hLA : 3 * (c * α) + 3 ≤ 7 * p := by
    have : c * α ≤ (√p + 1) * √p :=
      mul_le_mul hc hα hα0 (by positivity)
    nlinarith
  refine ⟨hLA, ?_, by linarith⟩
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  norm_num at hl1 hl2
  have hl0 : 0 < Real.log 2 := by linarith
  have h7 : Real.log (3 * (c * α) + 3) ≤ Real.log (7 * p) :=
    Real.log_le_log (by positivity) hLA
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 * p / 32 by positivity)
  have h2 : Real.log (7 * p / 32) = Real.log (7 * p) - 5 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), show (32 : ℝ) = 2 ^ 5 by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [Real.logb, div_le_iff₀ hl0]
  nlinarith [mul_le_mul_of_nonneg_left hl1.le (by linarith : (0 : ℝ) ≤ p)]

/-- precision budget for `E` ("Γ = ⌈29p⌉ and P = 34p suffice"): with
`m ≤ √p/4 + 1` (`α ≥ 2`), `L_A = 3m+1 ≤ p` and `log₂(F L_A) ≤ 1.14p + log₂ p`, and
`log₂ p ≤ 2.86p - 13`, so `p + 29p + ⌈log₂(F L_A)⌉ + 11 ≤ 34p` for `p ≥ 100` (last
conjunct, with `⌈x⌉ ≤ x + 1` and `F = 2^⌈1.14α²⌉`) -/
theorem budget_E (p : ℝ) (hp : 100 ≤ p) :
    3 * (√p / 4 + 1) + 1 ≤ p ∧ Real.logb 2 p ≤ 286 / 100 * p - 13 ∧
    p + 29 * p + ((114 / 100 * p + 1) + (286 / 100 * p - 13) + 1) + 11 ≤ 34 * p := by
  have hsq : √p ^ 2 = p := Real.sq_sqrt (by linarith)
  have hs0 := Real.sqrt_nonneg p
  refine ⟨by nlinarith, ?_, by linarith⟩
  have hl1 := Real.log_two_gt_d9
  norm_num at hl1
  have hl0 : 0 < Real.log 2 := by linarith
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < p by linarith)
  rw [Real.logb, div_le_iff₀ hl0]
  nlinarith [mul_le_mul_of_nonneg_left hl1.le (by linarith : (0 : ℝ) ≤ p)]

/-- cost: both windows are below `2p` (`m = ⌈√p⌉α < (√p+1)√p ≤ 2p`; `m ≤ √p/4 + 1 < 2p`) -/
theorem windows_lt_2p (p c α : ℝ) (hp : 100 ≤ p) (hc0 : 0 ≤ c) (hc : c ≤ √p + 1)
    (hα0 : 0 ≤ α) (hα : α < √p) : c * α < 2 * p ∧ √p / 4 + 1 < 2 * p := by
  have hsq : √p ^ 2 = p := Real.sq_sqrt (by linarith)
  have hs0 := Real.sqrt_nonneg p
  have hs10 : 10 ≤ √p := by nlinarith
  constructor
  · have : c * α ≤ (√p + 1) * α := mul_le_mul_of_nonneg_right hc hα0
    have : (√p + 1) * α < (√p + 1) * √p := mul_lt_mul_of_pos_left hα (by positivity)
    nlinarith
  · nlinarith

end PRChecksB.PR5Analytic
