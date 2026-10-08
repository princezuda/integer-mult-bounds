import PRChecksC.Common
import PRChecksC.Assembly
import PRChecksC.PR10

/-!
# PR #12: dimension-30 bit network with controlled batching, conditional κ = 12649/10¹¹

Source: PR head `35d31e3` (worktree `/home/user/prs/pr12`): `research/batched-followup/`
(`witness.py`, `verify.py`, `proof.tex`, `README.md`, `certificate.json`), which reuses
PR #10's `controlled_bit_rank_moment.counts(h=30, roles)`, `batched_network.complex_certificate`
and `bulk_complex_guard` unchanged.

**Taken as given** (outputs of running the h = 30 circuit, `certificate.json` `producer.checked`):
`c = 16089992` additions and `Q = 1425495` output uses, hence `R = c + Q = 17515487`.
The complex network, its moment `Ξ(1 - 7/10⁷) < 1` and the bulk guard are PR #10's,
proved in `PRChecksC.PR10` (same JSON values; `drift.py` checks PR #12's copies against them).
As in PR #10, the class structure, the controlled basis at h = 30 (`proof.tex` lines 68-79)
and the batching/recurrence lemmas are written arguments, not checked here.
-/

namespace PRChecksC.PR12

open PRChecksC Real

/-- TAKEN AS GIVEN: additions of the h = 30 producer (circuit output) -/
def c_add : ℕ := 16089992
/-- TAKEN AS GIVEN: designated output uses (circuit output) -/
def Q_out : ℕ := 1425495
def R : ℕ := c_add + Q_out
def h : ℕ := 30
def v : ℕ := Nat.choose 30 5
def m : ℕ := 30 ^ 3
def N : ℕ := v ^ 3
def W : ℕ := 2 * v ^ 2 * (v + R)
def L : ℕ := 3 * v ^ 2 * Nat.choose 30 2 * (30 - 2)
def D : ℕ := N - 2 * L
def s : ℕ := W * m - D
def Bb : ℕ := v ^ 2 * R
def a1 : ℕ := m - 2 * h
def a2 : ℕ := m - h ^ 2
def a3 : ℕ := (h ^ 2 - 1) * (h - 1)
def k1 : ℕ := 2 * a1 - m
def k2 : ℕ := 2 * a2 - m
def k3 : ℕ := 2 * a3 - m
def kc : ℕ := h ^ 2
def S1 : ℕ := s - (Bb * k1 + Bb * k2 + 2 * N * k3 + Bb * kc)

theorem bit_counts :
    R = 17515487 ∧ v = 142506 ∧ m = 27000 ∧ N = 2894006152890216 ∧
    W = 717195632319935496 ∧ L = 742052859715440 ∧ D = 1409900433459336 ∧
    s = 19364280662737824932664 ∧ Bb = 355703810007077532 ∧ 2 * N = 5788012305780432 := by
  simp only [v, m, N, W, L, D, s, R, Bb, c_add, Q_out]; norm_num [Nat.choose]

theorem bit_eta : ((D : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 3857 / 52973979000 := by
  simp only [v, m, N, W, L, D, R, c_add, Q_out]; norm_num [Nat.choose]

/-- `proof.tex` lines 86-99 -/
theorem bit_classes :
    a1 = 26940 ∧ a2 = 26100 ∧ a3 = 26071 ∧ k1 = 26880 ∧ k2 = 25200 ∧ k3 = 25142 ∧ kc = 900 ∧
    m - a1 = 60 ∧ m - a3 = 929 ∧ 2 * a1 > m ∧ 2 * a2 > m ∧ 2 * a3 > m ∧ kc + k2 = m - kc ∧
    S1 = 373570603170925665960 ∧ S1 + (Bb * k1 + Bb * k2 + 2 * N * k3 + Bb * kc) = s := by
  simp only [a1, a2, a3, k1, k2, k3, kc, S1, s, D, L, W, N, Bb, m, h, v, R, c_add, Q_out]
  norm_num [Nat.choose]

theorem bit_weights :
    ((S1 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 613175987 / 31784387400 ∧
    ((Bb * k1 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 1961734544 / 3973048425 ∧
    ((Bb * k2 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 122608409 / 264869895 ∧
    ((2 * N * k3 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 33174869 / 4414498250 ∧
    ((Bb * kc : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 17515487 / 1059479580 ∧
    (613175987 / 31784387400 + 1961734544 / 3973048425 + 122608409 / 264869895 +
      33174869 / 4414498250 + 17515487 / 1059479580 : ℚ) = 1 - 3857 / 52973979000 ∧
    ((k1 : ℕ) : ℚ) / (m : ℕ) = 224 / 225 ∧ ((k2 : ℕ) : ℚ) / (m : ℕ) = 14 / 15 ∧
    ((k3 : ℕ) : ℚ) / (m : ℕ) = 12571 / 13500 ∧ ((kc : ℕ) : ℚ) / (m : ℕ) = 1 / 30 := by
  have hS1 := (bit_classes).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hS1]
  simp only [W, N, Bb, a1, a2, a3, k1, k2, k3, kc, m, h, v, R, c_add, Q_out]
  norm_num [Nat.choose]

/-- the five logarithm bounds, each the 16-term series enclosure rounded up to `10⁻⁹` -/
theorem bit_logs :
    Real.log (1 / (1 / 27000)) ≤ 2040718429 / 200000000 ∧
    Real.log (1 / ((26880 : ℝ) / 27000)) ≤ 4454351 / 1000000000 ∧
    Real.log (1 / ((25200 : ℝ) / 27000)) ≤ 8624109 / 125000000 ∧
    Real.log (1 / ((25142 : ℝ) / 27000)) ≤ 8912139 / 125000000 ∧
    Real.log (1 / ((900 : ℝ) / 27000)) ≤ 1700598691 / 500000000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [one_div_one_div]; linarith [log_27000_lt]
  · refine log_inv_le _ (1 / 225) _ 8 (by norm_num) (by norm_num) (by norm_num) ?_
    unfold Up ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  · refine log_inv_le _ (1 / 15) _ 12 (by norm_num) (by norm_num) (by norm_num) ?_
    unfold Up ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  · refine log_inv_le _ (929 / 13500) _ 12 (by norm_num) (by norm_num) (by norm_num) ?_
    unfold Up ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  · rw [show (1 : ℝ) / ((900 : ℝ) / 27000) = 30 by norm_num]; linarith [log_30_lt]

theorem bit_moment_upper :
    (613175987 / 31784387400 / (1 - 253 / 10 ^ 9 * (2040718429 / 200000000)) +
      1961734544 / 3973048425 / (1 - 253 / 10 ^ 9 * (4454351 / 1000000000)) +
      122608409 / 264869895 / (1 - 253 / 10 ^ 9 * (8624109 / 125000000)) +
      33174869 / 4414498250 / (1 - 253 / 10 ^ 9 * (8912139 / 125000000)) +
      17515487 / 1059479580 / (1 - 253 / 10 ^ 9 * (1700598691 / 500000000)) : ℚ) =
      951397175334835659786955529971356627333020221426690409795882007543066085393917500000000000000 /
        951397175343791337554697540817110713134256690198498127782083171487866834310970992296187410241 ∧
    1 - (951397175334835659786955529971356627333020221426690409795882007543066085393917500000000000000 /
        951397175343791337554697540817110713134256690198498127782083171487866834310970992296187410241 : ℚ) =
      8955677767742010845754085801236468771807717986201163944800748917053492296187410241 /
        951397175343791337554697540817110713134256690198498127782083171487866834310970992296187410241 ∧
    (9 : ℚ) / 10 ^ 12 < 8955677767742010845754085801236468771807717986201163944800748917053492296187410241 /
        951397175343791337554697540817110713134256690198498127782083171487866834310970992296187410241 := by
  norm_num

/-- negative control (`verify.py`): the same certificate fails at `a = 254/10⁹` -/
theorem bit_moment_upper_254_fails :
    1 < (613175987 / 31784387400 / (1 - 254 / 10 ^ 9 * (2040718429 / 200000000)) +
      1961734544 / 3973048425 / (1 - 254 / 10 ^ 9 * (4454351 / 1000000000)) +
      122608409 / 264869895 / (1 - 254 / 10 ^ 9 * (8624109 / 125000000)) +
      33174869 / 4414498250 / (1 - 254 / 10 ^ 9 * (8912139 / 125000000)) +
      17515487 / 1059479580 / (1 - 254 / 10 ^ 9 * (1700598691 / 500000000)) : ℚ) := by
  norm_num

/-- **The certified bit saving `a_b = 253/10⁹`** (`proof.tex` lines 100-112) -/
theorem bit_moment :
    ((S1 : ℕ) : ℝ) / ((W : ℕ) * ((m : ℕ) : ℝ) ^ (1 - (253 / 10 ^ 9 : ℝ))) +
      ((Bb : ℕ) : ℝ) / (W : ℕ) * (((k1 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (253 / 10 ^ 9 : ℝ)) +
      ((Bb : ℕ) : ℝ) / (W : ℕ) * (((k2 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (253 / 10 ^ 9 : ℝ)) +
      ((2 * N : ℕ) : ℝ) / (W : ℕ) * (((k3 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (253 / 10 ^ 9 : ℝ)) +
      ((Bb : ℕ) : ℝ) / (W : ℕ) * (((kc : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (253 / 10 ^ 9 : ℝ)) < 1 := by
  obtain ⟨-, -, hm, -, hW, -, -, -, hBb, hN2⟩ := bit_counts
  obtain ⟨-, -, -, hk1, hk2, hk3, hkc, -, -, -, -, -, -, hS1, -⟩ := bit_classes
  rw [hS1, hW, hm, hBb, hN2, hk1, hk2, hk3, hkc]
  push_cast
  rw [singleton_form _ _ _ _ (by norm_num)]
  obtain ⟨l0, l1, l2, l3, l4⟩ := bit_logs
  have t0 := moment_term 373570603170925665960 717195632319935496 (1 / 27000) (253 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l0 (by norm_num)
  have t1 := moment_term 355703810007077532 717195632319935496 (26880 / 27000) (253 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l1 (by norm_num)
  have t2 := moment_term 355703810007077532 717195632319935496 (25200 / 27000) (253 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l2 (by norm_num)
  have t3 := moment_term 5788012305780432 717195632319935496 (25142 / 27000) (253 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l3 (by norm_num)
  have t4 := moment_term 355703810007077532 717195632319935496 (900 / 27000) (253 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l4 (by norm_num)
  have hsum : (373570603170925665960 : ℝ) * (1 / 27000) / 717195632319935496 /
        (1 - 253 / 10 ^ 9 * (2040718429 / 200000000)) +
      355703810007077532 * (26880 / 27000) / 717195632319935496 /
        (1 - 253 / 10 ^ 9 * (4454351 / 1000000000)) +
      355703810007077532 * (25200 / 27000) / 717195632319935496 /
        (1 - 253 / 10 ^ 9 * (8624109 / 125000000)) +
      5788012305780432 * (25142 / 27000) / 717195632319935496 /
        (1 - 253 / 10 ^ 9 * (8912139 / 125000000)) +
      355703810007077532 * (900 / 27000) / 717195632319935496 /
        (1 - 253 / 10 ^ 9 * (1700598691 / 500000000)) < 1 := by norm_num
  linarith

/-- other numbers in `proof.tex` and `README.md` -/
theorem proof_tex_numbers :
    (∀ j ∈ Finset.range 6, (Nat.choose j 2 + 2 * (if j = 2 then 1 else 0)) % 3 =
      if j = 5 then 1 else 0) ∧
    Nat.choose 30 4 = 27405 ∧ Nat.choose 5 2 * Nat.choose 25 3 = 23000 ∧
    2 * (h ^ 2 + h - 1) < h * h ^ 2 ∧ c_add + Q_out = 17515487 ∧ v = 142506 := by
  refine ⟨by decide, ?_⟩
  simp only [h, v, c_add, Q_out]; norm_num [Nat.choose]

/-! ## Assembly (`witness.py` `assembly`) -/

def P : Params where
  τ := 999999747 / 1000000000
  σ := 9999993 / 10000000
  ε := 49999993 / 100000000
  c := 1
  lam := 9999997470000001 / 10000000000000000
  lamp := 4999998735000001 / 5000000000000000
  κ := 12649 / 100000000000
  β := 1 / 1000
  δ := 1 / 10000000000
  C1 := 11999 / 10000

theorem parameter_origin :
    P.τ = 1 - 253 / 10 ^ 9 ∧ P.σ = 1 - 7 / 10 ^ 7 ∧ P.lam = P.τ + 1 / 10 ^ 16 ∧
    P.lamp = P.τ + 2 / 10 ^ 16 ∧ P.C1 = PR10.ρq - (PR10.ρq - 1) * P.β + PR10.ζq ∧
    P.σ = PR10.P.σ ∧ P.β = PR10.P.β ∧ P.C1 = PR10.P.C1 := by
  norm_num [P, PR10.P, PR10.ρq, PR10.ζq]

/-- exponents displayed in the PR's manuscript patch: `εC₁`, `1 - εC₁`, `α = Θ(p^((1-ε)/2))`,
`ℓ = Θ(p^(1-ε))`, `K = Θ(p^ε)`, and the prime-interval growth `p^(1-2ε)` -/
theorem patch_exponents :
    P.ε * P.C1 = 599949916007 / 1000000000000 ∧ 1 - P.ε * P.C1 = 400050083993 / 1000000000000 ∧ P.ε * P.C1 < 1 ∧
    (1 - P.ε) / 2 = 50000007 / 200000000 ∧ 1 - P.ε = 50000007 / 100000000 ∧ P.ε = 49999993 / 100000000 ∧
    1 - 2 * P.ε = 7 / 50000000 := by
  norm_num [P]

theorem recurrence_values :
    P.internal = 999999747 / 1000000000 ∧ P.leaf = 9999993007 / 10000000000 ∧
    P.preprocessing = 0 ∧ P.layer = 999999747 / 1000000000 := by
  norm_num [P]

theorem slack_values :
    P.tau_positive = 999999747 / 1000000000 ∧
    P.tau_below_one = 253 / 1000000000 ∧
    P.sigma_positive = 9999993 / 10000000 ∧
    P.sigma_below_one = 7 / 10000000 ∧
    P.c_positive = 1 ∧
    P.epsilon_positive = 49999993 / 100000000 ∧
    P.beta_positive = 1 / 1000 ∧
    P.beta_below_one = 999 / 1000 ∧
    P.lambda_above_tau = 1 / 10000000000000000 ∧
    P.lambda_above_sigma = 4470000001 / 10000000000000000 ∧
    P.lambda_below_one = 2529999999 / 10000000000000000 ∧
    P.packed_overhead = 1 / 10000000000000000 ∧
    P.lambda_prime_above_lambda = 1 / 10000000000000000 ∧
    P.leaf_cost = 2231500001 / 5000000000000000 ∧
    P.lambda_prime_below_one = 1264999999 / 5000000000000000 ∧
    P.guard_width = 400050083993 / 1000000000000 ∧
    P.crt_layout = 12650001771 / 100000000000000000 ∧
    P.gaussian_cost = 1399 / 10000000000 ∧
    P.prefix_cost = 7 / 50000000 ∧
    P.scalar_cost = 5000000699 / 10000000000 ∧
    P.delta_positive = 1 / 10000000000 ∧
    P.delta_below_one_eighth = 1249999999 / 10000000000 ∧
    P.prime_interval_growth = 7 / 50000000 ∧
    P.alpha_squared_theta_growth = 7 / 50000000 ∧
    P.K_smaller_than_ell = 7 / 50000000 ∧
    P.K_dominates_log_p = 49999993 / 100000000 ∧
    P.r_superpolynomial = 50000007 / 100000000 ∧
    P.kappa_positive = 12649 / 100000000000 ∧
    P.reserved_axes = 4999998735000001 / 5000000000000000 := by
  norm_num [P]

theorem constraints_strict : P.AllStrict := by
  unfold Params.AllStrict; norm_num [P]

theorem margin_values :
    P.g1 = 7 / 50000000 ∧
    P.g2 = 12649998229 / 100000000000000000 ∧
    P.g3 = 63249991095000007 / 500000000000000000000000 ∧
    P.g4 = 12650001771 / 100000000000000000 ∧
    P.g5 = 1399 / 10000000000 ∧
    P.g6 = 5000000699 / 10000000000 ∧
    P.g7 = 49999993 / 100000000 := by
  norm_num [P]

/-- **Headline**: `min g = g3 > κ = 12649/10¹¹ > 6149999/(5·10¹³)` (PR #10's κ),
gap `4991095000007/(5·10²³) ≈ 9.98219·10⁻¹²`, ratio `6324500/6149999 ≈ 1.0284` -/
theorem kappa_witness :
    P.G3Min ∧ P.g3 - P.κ = 4991095000007 / 500000000000000000000000 ∧
    PR10.P.κ < P.κ ∧ P.κ / PR10.P.κ = 6324500 / 6149999 ∧
    (102837 : ℚ) / 100000 < P.κ / PR10.P.κ ∧ P.κ / PR10.P.κ < 102838 / 100000 ∧
    1 - P.τ = 253 / 10 ^ 9 ∧ 1 - P.σ = 7 / 10 ^ 7 := by
  unfold Params.G3Min; norm_num [P, PR10.P]

/-- negative control (`verify.py`, `assembly(minimum_margin)`): with `κ` set to the minimum
margin, the absorption condition fails -/
theorem kappa_at_margin_rejected : ¬ ({ P with κ := P.g3 } : Params).G3Min := by
  unfold Params.G3Min
  intro h
  exact lt_irrefl _ h.2.2.2.2.2.2

/-- the rational moment bound of `bit_moment_upper` as a function of the role count `R'`
(same logarithm bounds, `a = 253/10⁹`) -/
def momentUpper (R' : ℕ) : ℚ :=
  let W' : ℚ := 2 * v ^ 2 * (v + R')
  let B' : ℚ := v ^ 2 * R'
  let s' : ℚ := W' * m - (N - 2 * L)
  let S' : ℚ := s' - (B' * k1 + B' * k2 + 2 * N * k3 + B' * kc)
  S' / (W' * m) / (1 - 253 / 10 ^ 9 * (2040718429 / 200000000)) +
    B' * k1 / (W' * m) / (1 - 253 / 10 ^ 9 * (4454351 / 1000000000)) +
    B' * k2 / (W' * m) / (1 - 253 / 10 ^ 9 * (8624109 / 125000000)) +
    2 * N * k3 / (W' * m) / (1 - 253 / 10 ^ 9 * (8912139 / 125000000)) +
    B' * kc / (W' * m) / (1 - 253 / 10 ^ 9 * (1700598691 / 500000000))

/-- negative control (`verify.py`, `bit(roles + 1000000)`): the certificate holds at the
producer's `R` and fails once `R` is inflated by `10⁶` -/
theorem inflated_roles_rejected : momentUpper R < 1 ∧ 1 < momentUpper (R + 1000000) := by
  simp only [momentUpper, R, c_add, Q_out, v, m, N, L, k1, k2, k3, kc, a1, a2, a3, h]
  norm_num [Nat.choose]

end PRChecksC.PR12
