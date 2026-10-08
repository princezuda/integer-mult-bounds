import PRChecksC.Common

/-!
# PR #11: no new κ; its negative screens

PR #11 (head `a97c1ba`, worktree `/home/user/prs/pr11`) adds `research/geometric-dimensions/`
on top of PR #9. Its head commit only records PR #10's posted claim
`κ = 6149999/50000000000000` (README line 10-16); `report.json` has status
"RESEARCH EXTENSIONS AND NEGATIVE SCREENS; NO NEW KAPPA". It makes **no new κ claim**.

Its arithmetic is negative: exact upper bounds on the unbatched bit saving that reject
six other dimensions and two prime-power families against PR #9's `761/10¹¹`
(`report.py`, `family.py`). We check that arithmetic here.

**Taken as given**: the six role counts `R_h` (circuit outputs, `report.json`
`dimensions[*].roles`), and the stated architecture-specific reductions of `family.py`
(e.g. `η ≤ 1/(2h³(1 + b))` for the q ≥ 7 and q = 5 tails), which are written arguments.
-/

namespace PRChecksC.PR11

open PRChecksC Real

/-- main's `certified_saving_le`: a certified `σ` with `r ≤ m^σ` has
`(1 - σ) log m ≤ (1 - r/m)/(r/m)` -/
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

/-- if `r = m (1 - η)` and `η < T (1 - η) ℓ` with `ℓ ≤ log m`, no certified saving reaches `T` -/
theorem saving_reject (m r η ℓ T σ' : ℝ) (hm : 1 < m) (hη0 : 0 < η) (hη1 : η < 1)
    (hr : r = m * (1 - η)) (hcert : r ≤ m ^ σ') (hℓ : ℓ ≤ Real.log m) (hℓ0 : 0 < ℓ)
    (hT0 : 0 < T) (hT : η < T * (1 - η) * ℓ) : 1 - σ' < T := by
  have hm0 : 0 < m := by linarith
  have hr0 : 0 < r := by rw [hr]; exact mul_pos hm0 (by linarith)
  have h1 := certified_saving_le m r σ' hm hr0 hcert
  have hrm : r / m = 1 - η := by rw [hr]; field_simp
  rw [hrm, show 1 - (1 - η) = η by ring] at h1
  have hη1' : 0 < 1 - η := by linarith
  have h2 : (1 - σ') * Real.log m * (1 - η) ≤ η := by
    rw [le_div_iff₀ hη1'] at h1; linarith
  by_contra hc
  push_neg at hc
  have hL : 0 < Real.log m := lt_of_lt_of_le hℓ0 hℓ
  have h3 : T * (1 - η) * Real.log m ≤ (1 - σ') * Real.log m * (1 - η) := by
    have := mul_le_mul_of_nonneg_right hc (mul_nonneg hL.le hη1'.le)
    nlinarith
  have h4 : T * (1 - η) * ℓ ≤ T * (1 - η) * Real.log m :=
    mul_le_mul_of_nonneg_left hℓ (mul_nonneg hT0.le hη1'.le)
  linarith

/-! ## Logarithm lower bounds -/

theorem log_13824_ge : (9534 : ℝ) / 1000 ≤ Real.log 13824 := by
  have h : Real.log 13824 = 9 * Real.log 2 + 3 * Real.log 3 := by
    have e : (13824 : ℝ) = 2 ^ 9 * 3 ^ 3 := by norm_num
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  rw [h]; linarith [log_two_bounds.1, log_three_bounds.1]

theorem log_19683_ge : (98875 : ℝ) / 10000 ≤ Real.log 19683 := by
  have h : Real.log 19683 = 9 * Real.log 3 := by
    have e : (19683 : ℝ) = 3 ^ 9 := by norm_num
    rw [e, Real.log_pow]; push_cast; ring
  rw [h]; linarith [log_three_bounds.1]

theorem log_27000_ge : (102035 : ℝ) / 10000 ≤ Real.log 27000 := by
  have h : Real.log 27000 = 3 * Real.log 2 + 3 * Real.log 3 + 3 * Real.log 5 := by
    have e : (27000 : ℝ) = 2 ^ 3 * 3 ^ 3 * 5 ^ 3 := by norm_num
    rw [e, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [h]; linarith [log_two_bounds.1, log_three_bounds.1, log_five_bounds.1]

theorem log_8000_ge : (898 : ℝ) / 100 ≤ Real.log 8000 := by
  have h : Real.log 8000 = 6 * Real.log 2 + 3 * Real.log 5 := by
    have e : (8000 : ℝ) = 2 ^ 6 * 5 ^ 3 := by norm_num
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  rw [h]; linarith [log_two_bounds.1, log_five_bounds.1]

theorem log_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Real.log a ≤ Real.log b :=
  Real.log_le_log ha hab

/-! ## The six dimension screens (`report.py`, `report.json` `dimensions`) -/

def v5 (h : ℕ) : ℕ := Nat.choose h 5
def mm (h : ℕ) : ℕ := h ^ 3
def WW (h R : ℕ) : ℕ := 2 * v5 h ^ 2 * (v5 h + R)
def LL (h : ℕ) : ℕ := 3 * v5 h ^ 2 * Nat.choose h 2 * (h - 2)
def DD (h : ℕ) : ℕ := v5 h ^ 3 - 2 * LL h
def ss (h R : ℕ) : ℕ := WW h R * mm h - DD h

/-- TAKEN AS GIVEN: role counts of the six screened producers (circuit outputs) -/
def R24 : ℕ := 4728452
def R26 : ℕ := 7602157
def R27 : ℕ := 9476476
def R29 : ℕ := 14398188
def R30 : ℕ := 17515487
def R32 : ℕ := 25224960

/-- the exact deficits `η_h = D/(W m) = (v - 6 C(h,2)(h-2))/(2 m (v + R))` -/
theorem screen_eta :
    ((DD 24 : ℕ) : ℚ) / ((WW 24 R24 : ℕ) * (mm 24 : ℕ)) = 253 / 5496141312 ∧
    ((DD 26 : ℕ) : ℚ) / ((WW 26 R26 : ℕ) * (mm 26 : ℕ)) = 365 / 5183525412 ∧
    ((DD 27 : ℕ) : ℚ) / ((WW 27 R27 : ℕ) * (mm 27 : ℕ)) = 260 / 3483601587 ∧
    ((DD 29 : ℕ) : ℚ) / ((WW 29 R29 : ℕ) * (mm 29 : ℕ)) = 3 / 40094414 ∧
    ((DD 30 : ℕ) : ℚ) / ((WW 30 R30 : ℕ) * (mm 30 : ℕ)) = 3857 / 52973979000 ∧
    ((DD 32 : ℕ) : ℚ) / ((WW 32 R32 : ℕ) * (mm 32 : ℕ)) = 3503 / 52073136128 := by
  simp only [DD, WW, LL, mm, v5, R24, R26, R27, R29, R30, R32]
  norm_num [Nat.choose]

/-- `s/W = m (1 - η)` for each screened dimension -/
theorem screen_ratio :
    ((ss 24 R24 : ℕ) : ℝ) / (WW 24 R24 : ℕ) = 13824 * (1 - 253 / 5496141312) ∧
    ((ss 26 R26 : ℕ) : ℝ) / (WW 26 R26 : ℕ) = 17576 * (1 - 365 / 5183525412) ∧
    ((ss 27 R27 : ℕ) : ℝ) / (WW 27 R27 : ℕ) = 19683 * (1 - 260 / 3483601587) ∧
    ((ss 29 R29 : ℕ) : ℝ) / (WW 29 R29 : ℕ) = 24389 * (1 - 3 / 40094414) ∧
    ((ss 30 R30 : ℕ) : ℝ) / (WW 30 R30 : ℕ) = 27000 * (1 - 3857 / 52973979000) ∧
    ((ss 32 R32 : ℕ) : ℝ) / (WW 32 R32 : ℕ) = 32768 * (1 - 3503 / 52073136128) := by
  simp only [ss, DD, WW, LL, mm, v5, R24, R26, R27, R29, R30, R32]
  norm_num [Nat.choose]

/-- **The six screens**: in each dimension, no certified unbatched bit saving reaches
PR #9's `761/10¹¹` (`report.json` `below_pr9_certified_bit_saving = true`). -/
theorem screens_reject (σ' : ℝ) :
    (((ss 24 R24 : ℕ) : ℝ) / (WW 24 R24 : ℕ) ≤ (13824 : ℝ) ^ σ' → 1 - σ' < 761 / 10 ^ 11) ∧
    (((ss 26 R26 : ℕ) : ℝ) / (WW 26 R26 : ℕ) ≤ (17576 : ℝ) ^ σ' → 1 - σ' < 761 / 10 ^ 11) ∧
    (((ss 27 R27 : ℕ) : ℝ) / (WW 27 R27 : ℕ) ≤ (19683 : ℝ) ^ σ' → 1 - σ' < 761 / 10 ^ 11) ∧
    (((ss 29 R29 : ℕ) : ℝ) / (WW 29 R29 : ℕ) ≤ (24389 : ℝ) ^ σ' → 1 - σ' < 761 / 10 ^ 11) ∧
    (((ss 30 R30 : ℕ) : ℝ) / (WW 30 R30 : ℕ) ≤ (27000 : ℝ) ^ σ' → 1 - σ' < 761 / 10 ^ 11) ∧
    (((ss 32 R32 : ℕ) : ℝ) / (WW 32 R32 : ℕ) ≤ (32768 : ℝ) ^ σ' → 1 - σ' < 761 / 10 ^ 11) := by
  obtain ⟨e24, e26, e27, e29, e30, e32⟩ := screen_ratio
  have l24 := log_13824_ge
  have l26 : (9534 : ℝ) / 1000 ≤ Real.log 17576 :=
    l24.trans (log_mono (by norm_num) (by norm_num))
  have l27 := log_19683_ge
  have l29 : (98875 : ℝ) / 10000 ≤ Real.log 24389 :=
    l27.trans (log_mono (by norm_num) (by norm_num))
  have l30 := log_27000_ge
  have l32 : (102035 : ℝ) / 10000 ≤ Real.log 32768 :=
    l30.trans (log_mono (by norm_num) (by norm_num))
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact saving_reject _ _ _ _ _ σ' (by norm_num) (by norm_num) (by norm_num) e24 h l24
      (by norm_num) (by norm_num) (by norm_num)
  · exact saving_reject _ _ _ _ _ σ' (by norm_num) (by norm_num) (by norm_num) e26 h l26
      (by norm_num) (by norm_num) (by norm_num)
  · exact saving_reject _ _ _ _ _ σ' (by norm_num) (by norm_num) (by norm_num) e27 h l27
      (by norm_num) (by norm_num) (by norm_num)
  · exact saving_reject _ _ _ _ _ σ' (by norm_num) (by norm_num) (by norm_num) e29 h l29
      (by norm_num) (by norm_num) (by norm_num)
  · exact saving_reject _ _ _ _ _ σ' (by norm_num) (by norm_num) (by norm_num) e30 h l30
      (by norm_num) (by norm_num) (by norm_num)
  · exact saving_reject _ _ _ _ _ σ' (by norm_num) (by norm_num) (by norm_num) e32 h l32
      (by norm_num) (by norm_num) (by norm_num)

/-! ## `family.py`: the q = 5 architecture (r = 9, t = 4, output factor 2) -/

/-- `cap(5, h, 2)`'s deficit fraction `η = (C(h,9) - 6 C(h,4)(h-4)) / (2h³(C(h,9) + 2 Q))`,
`Q = C(h,4)(C(h-4,5)+1)` -/
def q5num (h : ℕ) : ℤ := (Nat.choose h 9 : ℤ) - 6 * Nat.choose h 4 * (h - 4)
def q5den (h : ℕ) : ℤ :=
  2 * h ^ 3 * (Nat.choose h 9 + 2 * (Nat.choose h 4 * (Nat.choose (h - 4) 5 + 1)))

/-- `h = 14..23`: nonpositive deficit, so `cap = 0` (`family.py` asserts `h = 14` and lists
`15..23`) -/
theorem q5_nonpositive :
    q5num 14 ≤ 0 ∧ q5num 15 ≤ 0 ∧ q5num 16 ≤ 0 ∧ q5num 17 ≤ 0 ∧ q5num 18 ≤ 0 ∧ q5num 19 ≤ 0 ∧
    q5num 20 ≤ 0 ∧ q5num 21 ≤ 0 ∧ q5num 22 ≤ 0 ∧ q5num 23 ≤ 0 := by
  simp only [q5num]; norm_num [Nat.choose]

/-- `h = 24..29`: exact η, and `η < T (1-η) · 9.534 ≤ T (1-η) log(h³)` -/
theorem q5_rows :
    (q5num 24 : ℚ) / q5den 24 = 1 / 282439008 ∧
    (q5num 25 : ℚ) / q5den 25 = 71 / 2553843750 ∧
    (q5num 26 : ℚ) / q5den 26 = 77 / 1858802608 ∧
    (q5num 27 : ℚ) / q5den 27 = 2323 / 47877204762 ∧
    (q5num 28 : ℚ) / q5den 28 = 145 / 2810316992 ∧
    (q5num 29 : ℚ) / q5den 29 = 815 / 15611447678 ∧
    (1 / 282439008 : ℚ) < 761 / 10 ^ 11 * (1 - 1 / 282439008) * (9534 / 1000) ∧
    (71 / 2553843750 : ℚ) < 761 / 10 ^ 11 * (1 - 71 / 2553843750) * (9534 / 1000) ∧
    (77 / 1858802608 : ℚ) < 761 / 10 ^ 11 * (1 - 77 / 1858802608) * (9534 / 1000) ∧
    (2323 / 47877204762 : ℚ) < 761 / 10 ^ 11 * (1 - 2323 / 47877204762) * (9534 / 1000) ∧
    (145 / 2810316992 : ℚ) < 761 / 10 ^ 11 * (1 - 145 / 2810316992) * (9534 / 1000) ∧
    (815 / 15611447678 : ℚ) < 761 / 10 ^ 11 * (1 - 815 / 15611447678) * (9534 / 1000) := by
  simp only [q5num, q5den]; norm_num [Nat.choose]

/-- `log (h³) ≥ 9.534` for every `h ≥ 24` -/
theorem log_cube_ge (h : ℝ) (hh : 24 ≤ h) : (9534 : ℝ) / 1000 ≤ Real.log (h ^ 3) := by
  have : (13824 : ℝ) ≤ h ^ 3 := by nlinarith [sq_nonneg h, mul_pos (by linarith : (0:ℝ) < h) (by linarith : (0:ℝ) < h)]
  exact log_13824_ge.trans (log_mono (by norm_num) this)

/-- the q = 5 tail (`tail_cap(5, h, 2)`, stated reduction `η ≤ 1/(2h³·253)`): for every real
`h ≥ 30`, `η/((1-η) log h³) < 761/10¹¹` -/
theorem q5_tail (h η : ℝ) (hh : 30 ≤ h) (hη0 : 0 < η) (hη : η ≤ 1 / (2 * h ^ 3 * 253)) :
    η / ((1 - η) * Real.log (h ^ 3)) < 761 / 10 ^ 11 := by
  have h3 : (27000 : ℝ) ≤ h ^ 3 := by nlinarith [sq_nonneg h, mul_pos (by linarith : (0:ℝ) < h) (by linarith : (0:ℝ) < h)]
  have hL : (102035 : ℝ) / 10000 ≤ Real.log (h ^ 3) := log_27000_ge.trans (log_mono (by norm_num) h3)
  have hη1 : η ≤ 1 / (2 * 27000 * 253) := by
    refine hη.trans ?_
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hpos : 0 < (1 - η) * Real.log (h ^ 3) := mul_pos (by norm_num at hη1; linarith) (by linarith)
  rw [div_lt_iff₀ hpos]
  have : (1 - 1 / (2 * 27000 * 253) : ℝ) * (102035 / 10000) ≤ (1 - η) * Real.log (h ^ 3) := by
    apply mul_le_mul (by linarith) hL (by norm_num) (by norm_num at hη1; linarith)
  nlinarith

/-- the q ≥ 7 bound (`tail_cap(7, 20)`, stated reduction `η ≤ 1/(2h³(1+b))`, `b ≥ C(13,6)`):
for every real `h ≥ 20` and `b ≥ 1716`, `η/((1-η) log h³) < 761/10¹¹` -/
theorem q7_all (h b η : ℝ) (hh : 20 ≤ h) (hb : 1716 ≤ b) (hη0 : 0 < η)
    (hη : η ≤ 1 / (2 * h ^ 3 * (1 + b))) :
    η / ((1 - η) * Real.log (h ^ 3)) < 761 / 10 ^ 11 := by
  have h3 : (8000 : ℝ) ≤ h ^ 3 := by nlinarith [sq_nonneg h, mul_pos (by linarith : (0:ℝ) < h) (by linarith : (0:ℝ) < h)]
  have hL : (898 : ℝ) / 100 ≤ Real.log (h ^ 3) := log_8000_ge.trans (log_mono (by norm_num) h3)
  have hη1 : η ≤ 1 / (2 * 8000 * 1717) := by
    refine hη.trans ?_
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hpos : 0 < (1 - η) * Real.log (h ^ 3) := mul_pos (by norm_num at hη1; linarith) (by linarith)
  rw [div_lt_iff₀ hpos]
  have : (1 - 1 / (2 * 8000 * 1717) : ℝ) * (898 / 100) ≤ (1 - η) * Real.log (h ^ 3) := by
    apply mul_le_mul (by linarith) hL (by norm_num) (by norm_num at hη1; linarith)
  nlinarith

/-- `C(13,6) = 1716`, the binomial used for q = 7, and `C(9,4) = 126` for q = 5 -/
theorem family_binomials : Nat.choose 13 6 = 1716 ∧ 1 + 2 * Nat.choose 9 4 = 253 := by
  norm_num [Nat.choose]

end PRChecksC.PR11
