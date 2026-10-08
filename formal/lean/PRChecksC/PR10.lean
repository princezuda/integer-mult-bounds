import PRChecksC.Common
import PRChecksC.Assembly

/-!
# PR #10: batched recursive networks, conditional κ = 6149999/(5·10¹³) > 2⁻²³

Source: PR head `62691e3` (worktree `/home/user/prs/pr10`): `scripts/batched_network.py`,
`scripts/controlled_bit_rank_moment.py`, `scripts/batched_bit_rank_moment.py`,
`scripts/bulk_complex_guard.py`, `scripts/fast_gaussian.py`, the notes
`notes/batched-bit-rank-accounting.tex`, `notes/controlled-projector-basis.tex`,
`notes/batched-assembly.tex`, `notes/bulk-complex-guard.tex`, and the certificates
`certificates/batched-network.json`, `certificates/controlled-bit-rank-moment.json`.

**Taken as given** (outputs of running PR #7's circuits):
* `R = 11840940` auxiliary roles per invocation of the h = 28 ternary bit producer;
* `Rc = 93838` side roles of the paired complex producer.
Also taken from the written notes (not derivable by arithmetic): which edge classes exist and
their ranks/copy counts (three bit classes `m-2h`, `m-h²`, `(h²-1)(h-1)` with copies
`v²R, v²R, 2N`; two complex classes `m-2h`, `m-h²` with `v_c²(R_c+h+1)` copies), the
path bound `q = m + 6h`, the batching lemmas, and the induction of the depth guard.

What is proved: the counts, rank-mass identities, all logarithm bounds, the two
mixed-width moments `Ψ(1 - 246/10⁹) < 1` and `Ξ(1 - 7/10⁷) < 1` as real-number
inequalities, the intermediate `177/10⁹` moment, the bulk guard (Taylor bound, path
moments, `160000⁵ < m⁶`, `E`, `C_dep`, `C₀`, `C₁`), the 29 constraints, 7 margins and
`2⁻²³ < κ < min g`.
-/

namespace PRChecksC.PR10

open PRChecksC Real

/-! ## Bit network (PR #7 producer, h = 28) -/

/-- TAKEN AS GIVEN: PR #7 roles per invocation (circuit output) -/
def R : ℕ := 11840940
def h : ℕ := 28
def v : ℕ := Nat.choose 28 5
def m : ℕ := 28 ^ 3
def N : ℕ := v ^ 3
def W : ℕ := 2 * v ^ 2 * (v + R)
def L : ℕ := 3 * v ^ 2 * Nat.choose 28 2 * (28 - 2)
def D : ℕ := N - 2 * L
def s : ℕ := W * m - D
/-- copies of each auxiliary class, `B = v²R` -/
def Bb : ℕ := v ^ 2 * R
/-- ranks of the three large classes -/
def a1 : ℕ := m - 2 * h
def a2 : ℕ := m - h ^ 2
def a3 : ℕ := (h ^ 2 - 1) * (h - 1)
/-- contiguous middle blocks `2a - m` of the large-projector lemma, and the stage-two corner `h²` -/
def k1 : ℕ := 2 * a1 - m
def k2 : ℕ := 2 * a2 - m
def k3 : ℕ := 2 * a3 - m
def kc : ℕ := h ^ 2
/-- singleton count of the three-class certificate and after the controlled basis -/
def S0 : ℕ := s - (Bb * k1 + Bb * k2 + 2 * N * k3)
def S1 : ℕ := S0 - Bb * kc

theorem bit_counts :
    v = 98280 ∧ m = 21952 ∧ N = 949282431552000 ∧ W = 230640858616896000 ∧
    L = 284784729465600 ∧ D = 379712972620800 ∧ s = 5063027748645128371200 ∧
    Bb = 114371146876896000 ∧ 2 * N = 1898564863104000 := by
  simp only [v, m, N, W, L, D, s, R, Bb]; norm_num [Nat.choose]

theorem bit_eta : ((D : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 39 / 520019360 := by
  simp only [v, m, N, W, L, D, R]; norm_num [Nat.choose]

/-- the class table (accounting note lines 74-80, controlled basis lines 163-185) -/
theorem bit_classes :
    a1 = 21896 ∧ a2 = 21168 ∧ a3 = 21141 ∧ k1 = 21840 ∧ k2 = 20384 ∧ k3 = 20330 ∧ kc = 784 ∧
    m - a1 = 56 ∧ m - a2 = 784 ∧ m - a3 = 811 ∧
    2 * a1 > m ∧ 2 * a2 > m ∧ 2 * a3 > m ∧ k1 = m - 4 * h ∧ k2 = m - 2 * h ^ 2 ∧
    k3 = m - 2 * h ^ 2 - 2 * h + 2 ∧ kc + k2 = m - kc := by
  simp only [a1, a2, a3, k1, k2, k3, kc, m, h]; norm_num

theorem bit_singletons :
    S0 = 195222619248167347200 ∧ S1 = 105555640096680883200 ∧
    S1 + (Bb * k1 + Bb * k2 + 2 * N * k3 + Bb * kc) = s := by
  simp only [S0, S1, s, D, L, W, N, Bb, a1, a2, a3, k1, k2, k3, kc, m, h, v, R]
  norm_num [Nat.choose]

/-- accounting note lines 44-63: with `d_j = (a-1)(h-1)`, `a = h^(j-1)`, the data rank sum is
`2N Σ_j (d_j + h - 1) + N = 2Nm - N` (here over ℤ, for every `h` and `N`) -/
theorem data_rank_sum (h N : ℤ) :
    2 * N * (((1 - 1) * (h - 1) + h - 1) + ((h - 1) * (h - 1) + h - 1) +
      ((h ^ 2 - 1) * (h - 1) + h - 1)) + N = 2 * N * h ^ 3 - N := by
  ring

/-- rank-mass weights `w = copies·k/(W m)` of the five classes, summing to `1 - η` -/
theorem bit_weights :
    ((S1 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 10841531 / 520019360 ∧
    ((Bb * k1 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 12827685 / 26000968 ∧
    ((Bb * k2 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 855179 / 1857212 ∧
    ((2 * N * k3 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 20865 / 2736944 ∧
    ((Bb * kc : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 65783 / 3714424 ∧
    (10841531 / 520019360 + 12827685 / 26000968 + 855179 / 1857212 + 20865 / 2736944 +
      65783 / 3714424 : ℚ) = 1 - 39 / 520019360 ∧
    ((k1 : ℕ) : ℚ) / (m : ℕ) = 195 / 196 ∧ ((k2 : ℕ) : ℚ) / (m : ℕ) = 13 / 14 ∧
    ((k3 : ℕ) : ℚ) / (m : ℕ) = 10165 / 10976 ∧ ((kc : ℕ) : ℚ) / (m : ℕ) = 1 / 28 := by
  obtain ⟨-, hS1, -⟩ := bit_singletons
  rw [hS1]
  simp only [W, N, Bb, a1, a2, a3, k1, k2, k3, kc, m, h, v, R]
  norm_num [Nat.choose]

/-- the five rational logarithm bounds `log (1/r_i) ≤ ℓ_i` -/
theorem bit_logs :
    Real.log (1 / (1 / 21952)) ≤ 9997 / 1000 ∧
    Real.log (1 / ((21840 : ℝ) / 21952)) ≤ 16 / 3125 ∧
    Real.log (1 / ((20384 : ℝ) / 21952)) ≤ 7411 / 100000 ∧
    Real.log (1 / ((20330 : ℝ) / 21952)) ≤ 48 / 625 ∧
    Real.log (1 / ((784 : ℝ) / 21952)) ≤ 33323 / 10000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [one_div_one_div]; linarith [log_21952_lt]
  · refine log_inv_le _ (1 / 196) _ 6 (by norm_num) (by norm_num) (by norm_num) ?_
    unfold Up ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  · refine log_inv_le _ (1 / 14) _ 8 (by norm_num) (by norm_num) (by norm_num) ?_
    unfold Up ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  · refine log_inv_le _ (811 / 10976) _ 8 (by norm_num) (by norm_num) (by norm_num) ?_
    unfold Up ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  · rw [show (1 : ℝ) / ((784 : ℝ) / 21952) = 28 by norm_num]; linarith [log_28_lt]

/-- the exact rational moment `Σ w_i/(1 - a ℓ_i)` of the certificate, `a = 246/10⁹` -/
theorem bit_moment_upper :
    (10841531 / 520019360 / (1 - 246 / 10 ^ 9 * (9997 / 1000)) +
      12827685 / 26000968 / (1 - 246 / 10 ^ 9 * (16 / 3125)) +
      855179 / 1857212 / (1 - 246 / 10 ^ 9 * (7411 / 100000)) +
      20865 / 2736944 / (1 - 246 / 10 ^ 9 * (48 / 625)) +
      65783 / 3714424 / (1 - 246 / 10 ^ 9 * (33323 / 10000)) : ℚ) =
      832316498477146912564441713716480470146509771830369384326171875 /
        832316498516766812983714413733509306294639695517209061296295401 ∧
    1 - (832316498477146912564441713716480470146509771830369384326171875 /
        832316498516766812983714413733509306294639695517209061296295401 : ℚ) =
      39619900419272700017028836148129923686839676970123526 /
        832316498516766812983714413733509306294639695517209061296295401 ∧
    (476 : ℚ) / 10 ^ 13 < 39619900419272700017028836148129923686839676970123526 /
        832316498516766812983714413733509306294639695517209061296295401 := by
  norm_num

/-- **The certified bit saving `a_b = 246/10⁹`**: the controlled-basis normalized moment
`Ψ(τ) = S/(W m^τ) + Σ_i B_i/W (k_i/m)^τ` is `< 1` at `τ = 1 - 246/10⁹`. -/
theorem bit_moment :
    ((S1 : ℕ) : ℝ) / ((W : ℕ) * ((m : ℕ) : ℝ) ^ (1 - (246 / 10 ^ 9 : ℝ))) +
      ((Bb : ℕ) : ℝ) / (W : ℕ) * (((k1 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (246 / 10 ^ 9 : ℝ)) +
      ((Bb : ℕ) : ℝ) / (W : ℕ) * (((k2 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (246 / 10 ^ 9 : ℝ)) +
      ((2 * N : ℕ) : ℝ) / (W : ℕ) * (((k3 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (246 / 10 ^ 9 : ℝ)) +
      ((Bb : ℕ) : ℝ) / (W : ℕ) * (((kc : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (246 / 10 ^ 9 : ℝ)) < 1 := by
  obtain ⟨-, hm, -, hW, -, -, -, hBb, hN2⟩ := bit_counts
  obtain ⟨-, -, -, hk1, hk2, hk3, hkc, -⟩ := bit_classes
  obtain ⟨-, hS1, -⟩ := bit_singletons
  rw [hS1, hW, hm, hBb, hN2, hk1, hk2, hk3, hkc]
  push_cast
  rw [singleton_form _ _ _ _ (by norm_num)]
  obtain ⟨l0, l1, l2, l3, l4⟩ := bit_logs
  have t0 := moment_term 105555640096680883200 230640858616896000 (1 / 21952) (246 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l0 (by norm_num)
  have t1 := moment_term 114371146876896000 230640858616896000 (21840 / 21952) (246 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l1 (by norm_num)
  have t2 := moment_term 114371146876896000 230640858616896000 (20384 / 21952) (246 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l2 (by norm_num)
  have t3 := moment_term 1898564863104000 230640858616896000 (20330 / 21952) (246 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l3 (by norm_num)
  have t4 := moment_term 114371146876896000 230640858616896000 (784 / 21952) (246 / 10 ^ 9)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l4 (by norm_num)
  have hsum : (105555640096680883200 : ℝ) * (1 / 21952) / 230640858616896000 /
        (1 - 246 / 10 ^ 9 * (9997 / 1000)) +
      114371146876896000 * (21840 / 21952) / 230640858616896000 /
        (1 - 246 / 10 ^ 9 * (16 / 3125)) +
      114371146876896000 * (20384 / 21952) / 230640858616896000 /
        (1 - 246 / 10 ^ 9 * (7411 / 100000)) +
      1898564863104000 * (20330 / 21952) / 230640858616896000 /
        (1 - 246 / 10 ^ 9 * (48 / 625)) +
      114371146876896000 * (784 / 21952) / 230640858616896000 /
        (1 - 246 / 10 ^ 9 * (33323 / 10000)) < 1 := by norm_num
  linarith

/-- the intermediate three-class certificate (`batched_bit_rank_moment.py`, accounting note
lines 98-138): `Ψ(1 - 177/10⁹) < 1` with gap `> 1.78·10⁻¹⁰` -/
theorem bit_moment_177 :
    ((S0 : ℕ) : ℝ) / ((W : ℕ) * ((m : ℕ) : ℝ) ^ (1 - (177 / 10 ^ 9 : ℝ))) +
      ((Bb : ℕ) : ℝ) / (W : ℕ) * (((k1 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (177 / 10 ^ 9 : ℝ)) +
      ((Bb : ℕ) : ℝ) / (W : ℕ) * (((k2 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (177 / 10 ^ 9 : ℝ)) +
      ((2 * N : ℕ) : ℝ) / (W : ℕ) * (((k3 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (177 / 10 ^ 9 : ℝ))
      < 1 ∧
    (1 - (20051151 / 520019360 / (1 - 177 / 10 ^ 9 * (9997 / 1000)) +
      12827685 / 26000968 / (1 - 177 / 10 ^ 9 * (16 / 3125)) +
      855179 / 1857212 / (1 - 177 / 10 ^ 9 * (7411 / 100000)) +
      20865 / 2736944 / (1 - 177 / 10 ^ 9 * (48 / 625))) : ℚ) =
      9018851588112489028174294032233536762346739 /
        50604920044758147283008773507127786190942259516252989 ∧
    (178 : ℚ) / 10 ^ 12 < 9018851588112489028174294032233536762346739 /
        50604920044758147283008773507127786190942259516252989 ∧
    ((S0 : ℕ) : ℚ) / ((W : ℕ) * (m : ℕ)) = 20051151 / 520019360 := by
  obtain ⟨-, hm, -, hW, -, -, -, hBb, hN2⟩ := bit_counts
  obtain ⟨-, -, -, hk1, hk2, hk3, -, -⟩ := bit_classes
  obtain ⟨hS0, -, -⟩ := bit_singletons
  refine ⟨?_, by norm_num, by norm_num, ?_⟩
  · rw [hS0, hW, hm, hBb, hN2, hk1, hk2, hk3]
    push_cast
    rw [singleton_form _ _ _ _ (by norm_num)]
    obtain ⟨l0, l1, l2, l3, -⟩ := bit_logs
    have t0 := moment_term 195222619248167347200 230640858616896000 (1 / 21952) (177 / 10 ^ 9)
      _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l0 (by norm_num)
    have t1 := moment_term 114371146876896000 230640858616896000 (21840 / 21952) (177 / 10 ^ 9)
      _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l1 (by norm_num)
    have t2 := moment_term 114371146876896000 230640858616896000 (20384 / 21952) (177 / 10 ^ 9)
      _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l2 (by norm_num)
    have t3 := moment_term 1898564863104000 230640858616896000 (20330 / 21952) (177 / 10 ^ 9)
      _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l3 (by norm_num)
    have hsum : (195222619248167347200 : ℝ) * (1 / 21952) / 230640858616896000 /
          (1 - 177 / 10 ^ 9 * (9997 / 1000)) +
        114371146876896000 * (21840 / 21952) / 230640858616896000 /
          (1 - 177 / 10 ^ 9 * (16 / 3125)) +
        114371146876896000 * (20384 / 21952) / 230640858616896000 /
          (1 - 177 / 10 ^ 9 * (7411 / 100000)) +
        1898564863104000 * (20330 / 21952) / 230640858616896000 /
          (1 - 177 / 10 ^ 9 * (48 / 625)) < 1 := by norm_num
    linarith
  · rw [hS0]; simp only [W, m, v, R]; norm_num [Nat.choose]

/-! ## Complex network (PR #7 paired producer, h = 28) with whole-residual children -/

/-- TAKEN AS GIVEN: side roles of PR #7's paired complex producer (circuit output) -/
def Rc : ℕ := 93838
def vc : ℕ := Nat.choose 28 3
def aux : ℕ := Rc + h + 1
def Nc : ℕ := vc ^ 3
def Wc : ℕ := 2 * vc ^ 2 * (vc + aux)
def Lc : ℕ := 3 * vc ^ 2 * h * (h + 1)
def Dc : ℕ := 2 * Nc - 2 * Lc
def sc : ℕ := Wc * m - Dc
def Bc : ℕ := vc ^ 2 * aux
def c1 : ℕ := m - 2 * h
def c2 : ℕ := m - h ^ 2
def Sc : ℕ := sc - Bc * (c1 + c2)

/-- `notes/batched-assembly.tex` lines 4-36 -/
theorem complex_counts :
    vc = 3276 ∧ aux = 93867 ∧ Nc = 35158608576 ∧ Wc = 2085111546336 ∧ Lc = 26143580736 ∧
    Dc = 18030055680 ∧ sc = 45772350635112192 ∧ Bc = 1007397164592 ∧
    c1 = 21896 ∧ c2 = 21168 ∧ Sc = 2389799139122304 ∧
    Sc + Bc * c1 + Bc * c2 = sc ∧ (Wc : ℤ) * m - 2 * vc ^ 3 + 2 * Lc = sc := by
  simp only [vc, aux, Nc, Wc, Lc, Dc, sc, Bc, c1, c2, Sc, m, h, Rc]; norm_num [Nat.choose]

theorem complex_weights :
    ((Dc : ℕ) : ℚ) / ((Wc : ℕ) * (m : ℕ)) = 5 / 12693352 ∧
    ((Sc : ℕ) : ℚ) / ((Wc : ℕ) * (m : ℕ)) = 1325453 / 25386704 ∧
    ((Bc * c1 : ℕ) : ℚ) / ((Wc : ℕ) * (m : ℕ)) = 12233999 / 25386704 ∧
    ((Bc * c2 : ℕ) : ℚ) / ((Wc : ℕ) * (m : ℕ)) = 844803 / 1813336 ∧
    (1325453 / 25386704 + 12233999 / 25386704 + 844803 / 1813336 : ℚ) = 1 - 5 / 12693352 ∧
    ((c1 : ℕ) : ℚ) / (m : ℕ) = 391 / 392 ∧ ((c2 : ℕ) : ℚ) / (m : ℕ) = 27 / 28 := by
  obtain ⟨-, -, -, hW, -, hD, -, hB, hc1, hc2, hS, -⟩ := complex_counts
  rw [hW, hD, hB, hc1, hc2, hS]
  simp only [m]; norm_num

theorem complex_logs :
    Real.log (1 / (1 / 21952)) ≤ 9997 / 1000 ∧
    Real.log (1 / ((21896 : ℝ) / 21952)) ≤ 2555 / 10 ^ 6 ∧
    Real.log (1 / ((21168 : ℝ) / 21952)) ≤ 36368 / 10 ^ 6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [one_div_one_div]; linarith [log_21952_lt]
  · refine log_inv_le _ (1 / 392) _ 5 (by norm_num) (by norm_num) (by norm_num) ?_
    unfold Up ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  · refine log_inv_le _ (1 / 28) _ 6 (by norm_num) (by norm_num) (by norm_num) ?_
    unfold Up ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

theorem complex_moment_upper :
    (1325453 / 25386704 / (1 - 7 / 10 ^ 7 * (9997 / 1000)) +
      12233999 / 25386704 / (1 - 7 / 10 ^ 7 * (511 / 200000)) +
      844803 / 1813336 / (1 - 7 / 10 ^ 7 * (2273 / 62500)) : ℚ) =
      1525632527231324124285650786113750000000 / 1525632551364197359955324563293421369131 ∧
    1 - (1525632527231324124285650786113750000000 /
        1525632551364197359955324563293421369131 : ℚ) =
      24132873235669673777179671369131 / 1525632551364197359955324563293421369131 ∧
    (158 : ℚ) / 10 ^ 10 < 24132873235669673777179671369131 /
        1525632551364197359955324563293421369131 := by
  norm_num

/-- **The certified complex saving `a_c = 7/10⁷`**: `Ξ(1 - 7/10⁷) < 1` -/
theorem complex_moment :
    ((Sc : ℕ) : ℝ) / ((Wc : ℕ) * ((m : ℕ) : ℝ) ^ (1 - (7 / 10 ^ 7 : ℝ))) +
      ((Bc : ℕ) : ℝ) / (Wc : ℕ) * ((((c1 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (7 / 10 ^ 7 : ℝ)) +
        (((c2 : ℕ) : ℝ) / (m : ℕ)) ^ (1 - (7 / 10 ^ 7 : ℝ))) < 1 := by
  obtain ⟨-, -, -, hW, -, -, -, hB, hc1, hc2, hS, -⟩ := complex_counts
  obtain ⟨-, hm, -⟩ := bit_counts
  rw [hW, hB, hc1, hc2, hS, hm]
  push_cast
  rw [singleton_form _ _ _ _ (by norm_num), mul_add]
  obtain ⟨l0, l1, l2⟩ := complex_logs
  have t0 := moment_term 2389799139122304 2085111546336 (1 / 21952) (7 / 10 ^ 7)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l0 (by norm_num)
  have t1 := moment_term 1007397164592 2085111546336 (21896 / 21952) (7 / 10 ^ 7)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l1 (by norm_num)
  have t2 := moment_term 1007397164592 2085111546336 (21168 / 21952) (7 / 10 ^ 7)
    _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) l2 (by norm_num)
  have hsum : (2389799139122304 : ℝ) * (1 / 21952) / 2085111546336 /
        (1 - 7 / 10 ^ 7 * (9997 / 1000)) +
      1007397164592 * (21896 / 21952) / 2085111546336 / (1 - 7 / 10 ^ 7 * (2555 / 10 ^ 6)) +
      1007397164592 * (21168 / 21952) / 2085111546336 / (1 - 7 / 10 ^ 7 * (36368 / 10 ^ 6))
      < 1 := by norm_num
  linarith

/-! ## The bulk complex guard (`scripts/bulk_complex_guard.py`, `notes/bulk-complex-guard.tex`) -/

def q : ℕ := m + 6 * h
def E : ℕ := 64 * (Wc + m + 1) ^ 3
def Cdep : ℕ := 1000 * (E + 16 * m + 1)
def ζq : ℚ := 1 / 10000
def βq : ℚ := 1 / 1000
def ρq : ℚ := 6 / 5
/-- the common rational upper bound `θ̄` of the three path moments -/
def θbar : ℚ := 999 / 1000
/-- the rational lower bound for `m^ρ` -/
def mlow : ℕ := 160000
def C0 : ℕ := 16304044734034229354982033946533362986146411372544000

/-- the exact integer and rational guard inequalities -/
theorem guard_constants :
    q = 22120 ∧ 2 * c1 > q ∧ 2 * c2 > q ∧ c1 < m ∧ c2 < m ∧
    mlow ^ 5 < m ^ 6 ∧
    E = 580186831374453739191483276086074980416 ∧
    36 * Wc ^ 3 + 4 * sc + 4 * Wc + 8 * m + 4 < E ∧
    Cdep = 580186831374453739191483276086075331649000 ∧
    (E : ℚ) ≤ Cdep * (1 - θbar) ∧ 16 * m ≤ Cdep ∧
    -- `C0 = ⌈128 m (1 + 1/ζ) C_dep⌉`, an integer, and the completed-layer inequality
    (C0 : ℚ) = 128 * (m : ℚ) * (1 + 1 / ζq) * Cdep ∧
    (m : ℚ) * (1 + 1 / ζq) * Cdep + 18 ≤ C0 ∧
    ρq - (ρq - 1) * βq + ζq = 11999 / 10000 := by
  simp only [q, E, Cdep, C0, ζq, βq, ρq, θbar, mlow, c1, c2, Wc, sc, Dc, Nc, Lc, aux, vc, m, h,
    Rc]
  norm_num [Nat.choose]

/-- the upper bound `1 - 6t/5 + (3/25) t²/(1-t)` of `(1-t)^(6/5)` (`taylor_six_fifths`) -/
def taylorUp (t : ℚ) : ℚ := 1 - 6 / 5 * t + 3 / 25 * (t ^ 2 / (1 - t))

/-- the three rational path-moment upper bounds of note lines 104-110, below `θ̄` -/
theorem path_moment_rational :
    (q : ℚ) / mlow = 553 / 4000 ∧
    ((q : ℚ) - c1) / mlow + taylorUp (((m : ℚ) - c1) / m) = 47817969 / 47897500 ∧
    ((q : ℚ) - c2) / mlow + taylorUp (((m : ℚ) - c2) / m) = 1213697 / 1260000 ∧
    (553 / 4000 : ℚ) < θbar ∧ (47817969 / 47897500 : ℚ) < θbar ∧
    (1213697 / 1260000 : ℚ) < θbar ∧
    θbar - max (max (553 / 4000) (47817969 / 47897500)) (1213697 / 1260000 : ℚ) =
      63267 / 95795000 := by
  have hc1 : c1 = 21896 := by norm_num [c1, m, h]
  have hc2 : c2 = 21168 := by norm_num [c2, m, h]
  rw [hc1, hc2]
  norm_num [q, mlow, m, h, taylorUp, θbar]

/-- `mlow⁵ < m⁶` gives `m^ρ > mlow` -/
theorem m_rho_gt : (mlow : ℝ) < (m : ℝ) ^ ((ρq : ℚ) : ℝ) := by
  have hρ : ((ρq : ℚ) : ℝ) = 6 / 5 := by norm_num [ρq]
  have hm : (m : ℝ) = 21952 := by norm_num [m, h]
  have hl : (mlow : ℝ) = 160000 := by norm_num [mlow]
  rw [hρ, hm, hl]
  have hpos : 0 < (21952 : ℝ) ^ ((6 : ℝ) / 5) := by positivity
  have h5 : ((21952 : ℝ) ^ ((6 : ℝ) / 5)) ^ 5 = 21952 ^ 6 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show (6 / 5 : ℝ) * ((5 : ℕ) : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  by_contra hle
  push_neg at hle
  have := pow_le_pow_left₀ hpos.le hle 5
  rw [h5] at this
  norm_num at this

/-- **The path moments** (eq. `bulk-path-moments`), as real-number inequalities: the rational
bounds of `path_moment_rational`, `m^ρ > mlow` and `taylor_six_fifths` -/
theorem path_moments :
    (q : ℝ) / (m : ℝ) ^ ((ρq : ℚ) : ℝ) < (θbar : ℝ) ∧
    ((q : ℝ) - c1) / (m : ℝ) ^ ((ρq : ℚ) : ℝ) + ((c1 : ℝ) / m) ^ ((ρq : ℚ) : ℝ) < θbar ∧
    ((q : ℝ) - c2) / (m : ℝ) ^ ((ρq : ℚ) : ℝ) + ((c2 : ℝ) / m) ^ ((ρq : ℚ) : ℝ) < θbar := by
  obtain ⟨r0, r1, r2, s0, s1, s2, -⟩ := path_moment_rational
  have hc1n : c1 = 21896 := by norm_num [c1, m, h]
  have hc2n : c2 = 21168 := by norm_num [c2, m, h]
  have hqn : q = 22120 := by norm_num [q, m, h]
  have hmn : m = 21952 := by norm_num [m, h]
  have hθ : θbar = 999 / 1000 := rfl
  -- the rational bounds, with every definition evaluated
  rw [hqn, mlow] at r0
  rw [hqn, hmn, hc1n, mlow] at r1
  rw [hqn, hmn, hc2n, mlow] at r2
  rw [hθ] at s0 s1 s2
  unfold taylorUp at r1 r2
  have q0 := lt_of_eq_of_lt r0 s0
  have q1 := lt_of_eq_of_lt r1 s1
  have q2 := lt_of_eq_of_lt r2 s2
  simp only [Nat.cast_ofNat] at q0 q1 q2
  have e0 := (Rat.cast_lt (K := ℝ)).mpr q0
  have e1 := (Rat.cast_lt (K := ℝ)).mpr q1
  have e2 := (Rat.cast_lt (K := ℝ)).mpr q2
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_one] at e0 e1 e2
  have hM := m_rho_gt
  have hρ : ((ρq : ℚ) : ℝ) = 6 / 5 := by norm_num [ρq]
  have hθR : ((θbar : ℚ) : ℝ) = 999 / 1000 := by norm_num [θbar]
  rw [hρ, hmn, mlow] at hM
  rw [hρ, hθR, hqn, hc1n, hc2n, hmn]
  push_cast at hM ⊢
  have hd : ∀ x : ℝ, 0 < x → x / 21952 ^ ((6 : ℝ) / 5) < x / 160000 := fun x hx =>
    div_lt_div_of_pos_left hx (by norm_num) hM
  have t1 := taylor_six_fifths ((21952 - 21896) / 21952) (by norm_num) (by norm_num)
  have t2 := taylor_six_fifths ((21952 - 21168) / 21952) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - (21952 - 21896) / 21952 = 21896 / 21952 by norm_num] at t1
  rw [show (1 : ℝ) - (21952 - 21168) / 21952 = 21168 / 21952 by norm_num] at t2
  refine ⟨?_, ?_, ?_⟩
  · have := hd 22120 (by norm_num); linarith
  · have := hd (22120 - 21896) (by norm_num); linarith
  · have := hd (22120 - 21168) (by norm_num); linarith

/-- leaf absorption (note lines 129-133): `8 (2m)^(ρ-1) ≤ 16 m` -/
theorem leaf_absorption : 8 * (2 * 21952 : ℝ) ^ ((6 : ℝ) / 5 - 1) ≤ 16 * 21952 := by
  have : (2 * 21952 : ℝ) ^ ((6 : ℝ) / 5 - 1) ≤ (2 * 21952 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_one] at this
  linarith

/-- the induction step at an internal call (note lines 134-138): with `e ≥ d^β`,
`X = C d^(-β(ρ-1)) e^ρ ≥ C d^β ≥ C`, so `θ̄ X + E ≤ X` once `E ≤ (1 - θ̄) C` -/
theorem internal_step (C d β ρ e E : ℝ) (hd : 1 ≤ d) (hβ : 0 ≤ β) (hρ : 1 ≤ ρ)
    (he : d ^ β ≤ e) (hC : E ≤ C * (1 - (θbar : ℝ))) (hC0 : 0 ≤ C) :
    (θbar : ℝ) * (C * d ^ (-(β * (ρ - 1))) * e ^ ρ) + E ≤ C * d ^ (-(β * (ρ - 1))) * e ^ ρ := by
  have hθ : ((θbar : ℚ) : ℝ) = 999 / 1000 := by norm_num [θbar]
  rw [hθ] at hC ⊢
  have hd0 : 0 < d := by linarith
  have h1 : (d ^ β) ^ ρ ≤ e ^ ρ :=
    Real.rpow_le_rpow (Real.rpow_nonneg hd0.le _) he (by linarith)
  have h2 : d ^ (-(β * (ρ - 1))) * (d ^ β) ^ ρ = d ^ β := by
    rw [← Real.rpow_mul hd0.le, ← Real.rpow_add hd0]; congr 1; ring
  have h3 : 1 ≤ d ^ β := Real.one_le_rpow hd hβ
  have h4 : 0 ≤ d ^ (-(β * (ρ - 1))) := Real.rpow_nonneg hd0.le _
  have hX : C ≤ C * d ^ (-(β * (ρ - 1))) * e ^ ρ := by
    calc C ≤ C * d ^ β := le_mul_of_one_le_right hC0 h3
      _ = C * (d ^ (-(β * (ρ - 1))) * (d ^ β) ^ ρ) := by rw [h2]
      _ ≤ C * (d ^ (-(β * (ρ - 1))) * e ^ ρ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h4) hC0
      _ = C * d ^ (-(β * (ρ - 1))) * e ^ ρ := by ring
  linarith

/-! ## Assembly (`batched_network.py` `parameters`, `assembly`) -/

def P : Params where
  τ := 499999877 / 500000000
  σ := 9999993 / 10000000
  ε := 7999999 / 16000000
  c := 1
  lam := 9999997540000001 / 10000000000000000
  lamp := 4999998770000001 / 5000000000000000
  κ := 6149999 / 50000000000000
  β := 1 / 1000
  δ := 1 / 10000000000
  C1 := 11999 / 10000

/-- `notes/batched-assembly.tex` lines 71-101 -/
theorem parameter_origin :
    P.τ = 1 - 246 / 10 ^ 9 ∧ P.σ = 1 - 7 / 10 ^ 7 ∧ P.lam = 1 - 246 / 10 ^ 9 + 1 / 10 ^ 16 ∧
    P.lamp = 1 - 246 / 10 ^ 9 + 2 / 10 ^ 16 ∧ P.κ = 6149999 / (5 * 10 ^ 13) ∧
    P.C1 = ρq - (ρq - 1) * P.β + ζq ∧ P.σ < P.τ ∧
    P.leaf = 1 - 6993 / 10 ^ 10 ∧ P.leaf < P.τ ∧ 1 - P.ε * (1 + P.c) = 1 / 8000000 ∧
    1 - P.ε * P.C1 = 64008011999 / 160000000000 := by
  norm_num [P, ρq, ζq]

/-- exponents displayed in the PR's manuscript patch: `εC₁`, `1 - εC₁`, `α = Θ(p^((1-ε)/2))`,
`ℓ = Θ(p^(1-ε))`, `K = Θ(p^ε)`, and the prime-interval growth `p^(1-2ε)` -/
theorem patch_exponents :
    P.ε * P.C1 = 95991988001 / 160000000000 ∧ 1 - P.ε * P.C1 = 64008011999 / 160000000000 ∧ P.ε * P.C1 < 1 ∧
    (1 - P.ε) / 2 = 8000001 / 32000000 ∧ 1 - P.ε = 8000001 / 16000000 ∧ P.ε = 7999999 / 16000000 ∧
    1 - 2 * P.ε = 1 / 8000000 := by
  norm_num [P]

theorem recurrence_values :
    P.internal = 499999877 / 500000000 ∧ P.leaf = 9999993007 / 10000000000 ∧
    P.preprocessing = 0 ∧ P.layer = 499999877 / 500000000 := by
  norm_num [P]

theorem slack_values :
    P.tau_positive = 499999877 / 500000000 ∧
    P.tau_below_one = 123 / 500000000 ∧
    P.sigma_positive = 9999993 / 10000000 ∧
    P.sigma_below_one = 7 / 10000000 ∧
    P.c_positive = 1 ∧
    P.epsilon_positive = 7999999 / 16000000 ∧
    P.beta_positive = 1 / 1000 ∧
    P.beta_below_one = 999 / 1000 ∧
    P.lambda_above_tau = 1 / 10000000000000000 ∧
    P.lambda_above_sigma = 4540000001 / 10000000000000000 ∧
    P.lambda_below_one = 2459999999 / 10000000000000000 ∧
    P.packed_overhead = 1 / 10000000000000000 ∧
    P.lambda_prime_above_lambda = 1 / 10000000000000000 ∧
    P.leaf_cost = 2266500001 / 5000000000000000 ∧
    P.lambda_prime_below_one = 1229999999 / 5000000000000000 ∧
    P.guard_width = 64008011999 / 160000000000 ∧
    P.crt_layout = 984000123 / 8000000000000000 ∧
    P.gaussian_cost = 1249 / 10000000000 ∧
    P.prefix_cost = 1 / 8000000 ∧
    P.scalar_cost = 312500039 / 625000000 ∧
    P.delta_positive = 1 / 10000000000 ∧
    P.delta_below_one_eighth = 1249999999 / 10000000000 ∧
    P.prime_interval_growth = 1 / 8000000 ∧
    P.alpha_squared_theta_growth = 1 / 8000000 ∧
    P.K_smaller_than_ell = 1 / 8000000 ∧
    P.K_dominates_log_p = 7999999 / 16000000 ∧
    P.r_superpolynomial = 8000001 / 16000000 ∧
    P.kappa_positive = 6149999 / 50000000000000 ∧
    P.reserved_axes = 4999998770000001 / 5000000000000000 := by
  norm_num [P]

theorem constraints_strict : P.AllStrict := by
  unfold Params.AllStrict; norm_num [P]

theorem margin_values :
    P.g1 = 1 / 8000000 ∧
    P.g2 = 983999877 / 8000000000000000 ∧
    P.g3 = 9839998762000001 / 80000000000000000000000 ∧
    P.g4 = 984000123 / 8000000000000000 ∧
    P.g5 = 1249 / 10000000000 ∧
    P.g6 = 312500039 / 625000000 ∧
    P.g7 = 7999999 / 16000000 := by
  norm_num [P]

/-- **Headline**: `min g = g3 > κ = 6149999/(5·10¹³) = 1.2299998·10⁻⁷ > 2⁻²³` -/
theorem kappa_witness :
    P.G3Min ∧ P.g3 - P.κ = 362000001 / 80000000000000000000000 ∧
    (1 : ℚ) / 2 ^ 23 < P.κ ∧ P.κ - 1 / 2 ^ 23 = 194083351 / 51200000000000000 ∧
    P.κ = 12299998 / 10 ^ 14 ∧ 1 - P.τ = 246 / 10 ^ 9 ∧ 1 - P.σ = 7 / 10 ^ 7 := by
  unfold Params.G3Min; norm_num [P]

end PRChecksC.PR10
