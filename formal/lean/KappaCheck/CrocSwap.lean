import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Size
import Mathlib.Data.Complex.ExponentialBounds
import KappaCheck.Network
import KappaCheck.Certificates

/-!
# Formal check of the arithmetic in CrocSwap/integer-mult-bounds, κ = 83/10¹²

Source: `certificates/compact-control-layer.json` and `certificates/paired-network.json`
at commit `6e564879f51ae16f23d392e9e196c605f36d90df`, produced by
`scripts/compact_control_layer.py`, `scripts/certify.py`, `scripts/prepare_layers.py`
and `scripts/paired_network.py`.

What is checked here:

* **A.** the original complex network at `h = 25`: counts, positive deficit, and the
  exponent certificate `s_c / W_c < m ^ σ` with `1 - σ = 418/10¹²`;
* **B.** the paired bit network at `h = 50`, *given* its circuit's side-role count
  `R = 509194` per invocation: counts, deficit, and `s_b / W_b < m ^ τ` with
  `1 - τ = 296/10¹¹`;
* **C.** the generalized guard constants (`C1 = 5 - 4β + ζ`, `C0`, `s_c < m^5`, …);
* **D.** all 31 constraint slacks, the recurrence exponents, the seven margins, the
  minimum margin `g3 = 333833/(4·10¹⁵)` and `2^-34 < κ = 83/10¹² < g3`;
* **E.** the repair density bound `2n/2^G + 8n/2^(K-G) ≤ 5/(128 p³)` for all `p`;
* **F.** the per-level bounds behind their recurrence exponents
  `internal = τ + (1-β) max(σ-τ, 0)` and `leaf = σ + β(1-σ)`.

Not checked: the written tape constructions (compact-control movement, reservations,
repair, guard proof, complex-network interface), the circuit producing `R`, and the
upstream theorem.  Those remain the responsibility of the cited proofs.
-/

namespace KappaCheck.CrocSwap

open KappaCheck.Network KappaCheck.Certificates Real

/-! ## Logarithm bounds -/

/-- `log y < n (q - 1)` whenever `y ≤ q^n`, `n > 0` and `q ≠ 1` -/
theorem log_le_of_pow (y q : ℝ) (n : ℕ) (hy : 0 < y) (hq : 0 < q) (hq1 : q ≠ 1) (hn : 0 < n)
    (h : y ≤ q ^ n) : Real.log y < n * (q - 1) := by
  calc Real.log y ≤ Real.log (q ^ n) := Real.log_le_log hy h
    _ = n * Real.log q := by rw [Real.log_pow]
    _ < n * (q - 1) := by
        gcongr; exact Real.log_lt_sub_one_of_pos hq hq1

/-- `log (2^k · 15625/16384) < k · 0.6931471808 + 256 (q - 1)` -/
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

/-- upper bound used for the complex network, `m = 25^3 = 15625 = 2^14 · 15625/16384` -/
def L25 : ℚ := 14 * (6931471808 / 10 ^ 10) + 256 * (9998147318001 / 10 ^ 13 - 1)

theorem log_15625 : Real.log 15625 < (L25 : ℝ) := by
  have := log_split 14
  rw [show (2 : ℝ) ^ 14 * (15625 / 16384) = 15625 by norm_num] at this
  unfold L25; push_cast; linarith

/-- the note's stated bound `log m_c < 966/100` -/
theorem log_15625_note : Real.log 15625 < 966 / 100 := by
  have h := log_15625
  have : (L25 : ℝ) < 966 / 100 := by unfold L25; norm_num
  linarith

/-- their bound `log 125000 < 11.737`, with `125000 = 2^17 · 15625/16384` -/
theorem log_125000 : Real.log 125000 < 11737 / 1000 := by
  have := log_split 17
  rw [show (2 : ℝ) ^ 17 * (15625 / 16384) = 125000 by norm_num] at this
  norm_num at this ⊢; linarith

/-! ## A. The complex network at `h = 25` (original construction) -/

theorem complex25_counts :
    v 25 = 2300 ∧ m 25 = 15625 ∧ N 25 = 12167000000 ∧ Wc 25 = 58645352620000 ∧
    sc 25 = 916333630984500000 ∧ Lc 25 = 10315500000 ∧ Lc 25 < N 25 := by
  simp only [N, m, I, zc, Wc, Lc, sc, v]; norm_num [Nat.choose]

theorem complex25_eta :
    ((Wc 25 * m 25 - sc 25 : ℕ) : ℚ) / (Wc 25 * m 25) = 14 / 3464399375 := by
  simp only [N, m, I, zc, Wc, Lc, sc, v]; norm_num [Nat.choose]

/-- `1 - σ = 418/10¹²` is certified for the `h = 25` complex network -/
theorem complex25_exponent :
    ((sc 25 : ℕ) : ℝ) / (Wc 25 : ℕ) < (15625 : ℝ) ^ (1 - (418 / 10 ^ 12 : ℝ)) := by
  obtain ⟨-, -, -, hW, hs, -, -⟩ := complex25_counts
  rw [hs, hW]
  apply exponent_certificate 15625 (966 / 100) (418 / 10 ^ 12) (14 / 3464399375) _
    (by norm_num) (by norm_num) log_15625_note
  · norm_num
  · norm_num

/-! ## B. The paired bit network at `h = 50`

The side-role count `R = 509194` per invocation is produced by their circuit
(`SharedPointCircuit(50, PairedExclusionCircuit(49))`) and is taken as given.
Their count formulas (`scripts/shared_point_network.py`) are
`W = 2N + 2v²(R + h)`, `L = 3v²h²`, `D = N - 2L`, `s = W m - D`. -/

def R50 : ℕ := 509194
def Wp : ℕ := 2 * N 50 + 2 * v 50 ^ 2 * (R50 + 50)
def Lp : ℕ := 3 * v 50 ^ 2 * 50 ^ 2
def Dp : ℕ := N 50 - 2 * Lp
def sp : ℕ := Wp * m 50 - Dp

theorem bit50_counts :
    v 50 = 19600 ∧ m 50 = 125000 ∧ N 50 = 7529536000000 ∧ Wp = 406321422080000 ∧
    Lp = 2881200000000 ∧ Dp = 1767136000000 ∧ sp = 50790175992864000000 := by
  simp only [Wp, Lp, Dp, sp, R50, N, m, v]; norm_num [Nat.choose]

theorem bit50_eta : ((Dp : ℕ) : ℚ) / (Wp * m 50) = 23 / 661055000 := by
  simp only [Wp, Lp, Dp, R50, N, m, v]; norm_num [Nat.choose]

/-- `1 - τ = 296/10¹¹` is certified for the paired bit network -/
theorem bit50_exponent :
    ((sp : ℕ) : ℝ) / (Wp : ℕ) < (125000 : ℝ) ^ (1 - (296 / 10 ^ 11 : ℝ)) := by
  obtain ⟨-, -, -, hW, -, -, hs⟩ := bit50_counts
  rw [hs, hW]
  apply exponent_certificate 125000 (11737 / 1000) (296 / 10 ^ 11) (23 / 661055000) _
    (by norm_num) (by norm_num) log_125000
  · norm_num
  · norm_num

/-! ## C. Generalized guard constants (`scripts/prepare_layers.py`, `guard`) -/

def Eg : ℕ := 64 * (Wc 25 + m 25 + 1) ^ 3
def Bg : ℕ := sc 25 + Eg
def βq : ℚ := 1 / 1000
def ζq : ℚ := 1 / 10000
def C1q : ℚ := 5 - 4 * βq + ζq
def C0n : ℕ :=
  468702768364541266454706053568350325710944743089798636762052552973306387134258934583461152000000

theorem guard_constants :
    Eg = 12908648646364723556470023518520280006040064 ∧
    Bg = 12908648646364723556470024434853910990540064 ∧
    3 ≤ m 25 ∧ 2 ≤ sc 25 ∧ sc 25 < m 25 ^ 5 ∧
    sc 25 * (8 + Eg) ≤ 9 * Bg ^ 2 ∧ C1q = 49961 / 10000 ∧
    -- `C0 = ⌈max(128 m B², 18 m B² (1 + 1/ζ))⌉` and the whole-layer inequality
    (C0n : ℚ) = max (128 * 15625 * (Bg : ℚ) ^ 2) (18 * 15625 * (Bg : ℚ) ^ 2 * (1 + 1 / ζq)) ∧
    9 * 15625 * (Bg : ℚ) ^ 2 * (1 + 1 / ζq) + 18 ≤ C0n := by
  simp only [Eg, Bg, C1q, βq, ζq, C0n, N, m, I, zc, Wc, Lc, sc, v]
  norm_num [Nat.choose]

/-! ## D. Parameters, slacks, recurrence exponents and margins -/

def τ : ℚ := 12499999963 / 12500000000
def σ : ℚ := 499999999791 / 500000000000
def ε : ℚ := 1999 / 10000
def c : ℚ := 1 / 5
def lam : ℚ := 3999999998329 / 4000000000000
def lamp : ℚ := 399999999833 / 400000000000
def κ : ℚ := 83 / 1000000000000
def β : ℚ := 1 / 1000
def δ : ℚ := 1 / 1000000
def C1 : ℚ := 49961 / 10000

/-- the parameters are the ones derived from the certified savings -/
theorem parameter_origin : τ = 1 - 296 / 10 ^ 11 ∧ σ = 1 - 418 / 10 ^ 12 ∧ C1 = C1q := by
  norm_num [τ, σ, C1, C1q, βq, ζq]

def internal : ℚ := τ + (1 - β) * max (σ - τ) 0
def leaf : ℚ := σ + β * (1 - σ)
def prep : ℚ := max 0 (1 - c)
def layer : ℚ := max (max internal leaf) (max (1 - c) 0)

theorem recurrence_values :
    internal = 499999999789729 / 500000000000000 ∧
    leaf = 499999999791209 / 500000000000000 ∧
    prep = 4 / 5 ∧ layer = 499999999791209 / 500000000000000 := by
  norm_num [internal, leaf, prep, layer, τ, σ, β, c]

/-- all 31 constraint slacks of `constraints(..., 'nonadjacent', 'tight-gaussian')`,
with `packed_overhead` and `reserved_axes` replaced as in `compact_control_layer.py` -/
theorem constraint_slacks :
    0 < τ ∧ 0 < 1 - τ ∧ 0 < σ ∧ 0 < 1 - σ ∧ 0 < c ∧ 0 < ε ∧ 0 < β ∧ 0 < 1 - β ∧
    0 < lam - τ ∧ 0 < lam - σ ∧ 0 < 1 - lam ∧
    0 < lam - internal ∧                      -- packed_overhead (compact controls)
    0 < lamp - lam ∧ 0 < lamp - (σ + β * (1 - σ)) ∧ 0 < 1 - lamp ∧
    0 < 1 - ε * C1 ∧                          -- guard_width
    0 < 1 / 3 - ε ∧                           -- dimension_upper_bound
    0 < 1 - τ - ε * (1 - τ) ∧                 -- crt_layout (nonadjacent)
    0 < 1 / 4 - δ - 5 / 4 * ε ∧               -- gaussian_cost (tight)
    0 < 1 - ε * (1 + c) ∧ 0 < 1 - δ - ε ∧ 0 < δ ∧ 0 < 1 / 8 - δ ∧
    0 < 1 - 2 * ε ∧ 0 < 1 / 4 - ε / 4 ∧ 0 < 1 / 2 - 3 / 2 * ε ∧
    0 < 1 - ε - ε * c ∧ 0 < ε * c ∧ 0 < 1 - ε ∧ 0 < κ ∧
    0 < lamp - prep := by                     -- reserved_axes
  norm_num [τ, σ, ε, c, lam, lamp, κ, β, δ, C1, internal, prep]

/-- the stated slack values in the JSON certificate are exact -/
theorem slack_values :
    lam - internal = 349 / 125000000000000 ∧ lamp - prep = 79999999833 / 400000000000 ∧
    1 - ε * C1 = 127961 / 100000000 ∧ lamp - (σ + β * (1 - σ)) = 41 / 500000000000000 ∧
    lamp - lam = 1 / 4000000000000 ∧ lam - σ = 1 / 4000000000000 ∧
    lam - τ = 10169 / 4000000000000 ∧ 1 / 4 - δ - 5 / 4 * ε = 31 / 250000 ∧
    1 - lam = 1671 / 4000000000000 ∧ 1 - lamp = 167 / 400000000000 ∧
    1 / 3 - ε = 4003 / 30000 ∧ 1 - τ - ε * (1 - τ) = 296037 / 125000000000000 ∧
    1 - ε * (1 + c) = 19003 / 25000 ∧ 1 - δ - ε = 800099 / 1000000 ∧
    1 / 8 - δ = 124999 / 1000000 ∧ 1 - 2 * ε = 3001 / 5000 ∧
    1 / 4 - ε / 4 = 8001 / 40000 ∧ 1 / 2 - 3 / 2 * ε = 4003 / 20000 ∧
    1 - ε - ε * c = 19003 / 25000 ∧ ε * c = 1999 / 50000 ∧ 1 - ε = 8001 / 10000 ∧
    1 - τ = 37 / 12500000000 ∧ 1 - σ = 209 / 500000000000 ∧ 1 - β = 999 / 1000 := by
  norm_num [τ, σ, ε, c, lam, lamp, β, δ, C1, internal, prep]

def g1 : ℚ := 1 - ε * (1 + c)
def g2 : ℚ := ε * c * (1 - τ)
def g3 : ℚ := ε * (1 - lamp)
def g4 : ℚ := 1 - τ - ε * (1 - τ)
def g5 : ℚ := 1 / 4 - δ - 5 / 4 * ε
def g6 : ℚ := 1 - δ - ε
def g7 : ℚ := ε

theorem margin_values :
    g1 = 19003 / 25000 ∧ g2 = 73963 / 625000000000000 ∧ g3 = 333833 / 4000000000000000 ∧
    g4 = 296037 / 125000000000000 ∧ g5 = 31 / 250000 ∧ g6 = 800099 / 1000000 ∧
    g7 = 1999 / 10000 := by
  norm_num [g1, g2, g3, g4, g5, g6, g7, τ, ε, c, lamp, δ]

/-- `g3` is the minimum margin, it exceeds `κ`, and `2^-34 < κ < 2^-33` -/
theorem kappa_witness :
    g3 ≤ g1 ∧ g3 ≤ g2 ∧ g3 ≤ g4 ∧ g3 ≤ g5 ∧ g3 ≤ g6 ∧ g3 ≤ g7 ∧
    κ < g3 ∧ g3 - κ = 1833 / 4000000000000000 ∧
    (1 : ℚ) / 2 ^ 34 < κ ∧ κ < 1 / 2 ^ 33 := by
  norm_num [g1, g2, g3, g4, g5, g6, g7, τ, ε, c, lamp, δ, κ]

/-! ## E. Repair density, for every `p ≥ 2`

`guard_width p = 4 ℓ + 6` with `ℓ` the bit length of `p - 1` (`Nat.size`). For
`n ≤ p` and `K ≥ G + 4ℓ + 10`, the bad fraction `2n/2^G + 8n/2^(K-G)` is at most
`5/(128 p³)` (`scripts/compact_control_layer.py`, `repair_bound`). -/

theorem repair_bound (p n K : ℕ) (hp : 2 ≤ p) (hn : n ≤ p)
    (hK : 4 * Nat.size (p - 1) + 6 + 4 * Nat.size (p - 1) + 10 ≤ K) :
    (2 * n : ℚ) / 2 ^ (4 * Nat.size (p - 1) + 6) +
      8 * n / 2 ^ (K - (4 * Nat.size (p - 1) + 6)) ≤ 5 / (128 * p ^ 3) := by
  have hpl0 : p ≤ 2 ^ Nat.size (p - 1) := by
    have := Nat.lt_size_self (p - 1); omega
  set ℓ := Nat.size (p - 1)
  have hpl : p ≤ 2 ^ ℓ := hpl0
  have hpl' : (p : ℚ) ≤ 2 ^ ℓ := by exact_mod_cast hpl
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hn' : (n : ℚ) ≤ p := by exact_mod_cast hn
  have hG : (64 : ℚ) * p ^ 4 ≤ 2 ^ (4 * ℓ + 6) := by
    rw [pow_add, pow_mul]
    have : (p : ℚ) ^ 4 ≤ (2 ^ ℓ) ^ 4 := pow_le_pow_left₀ hp0.le hpl' 4
    rw [show ((2 : ℚ) ^ 4) ^ ℓ = (2 ^ ℓ) ^ 4 by rw [← pow_mul, ← pow_mul, mul_comm]]
    nlinarith
  have hKG : (1024 : ℚ) * p ^ 4 ≤ 2 ^ (K - (4 * ℓ + 6)) := by
    have hle : 4 * ℓ + 10 ≤ K - (4 * ℓ + 6) := by omega
    calc (1024 : ℚ) * p ^ 4 ≤ 2 ^ (4 * ℓ + 10) := by
          rw [pow_add, pow_mul]
          have : (p : ℚ) ^ 4 ≤ (2 ^ ℓ) ^ 4 := pow_le_pow_left₀ hp0.le hpl' 4
          rw [show ((2 : ℚ) ^ 4) ^ ℓ = (2 ^ ℓ) ^ 4 by rw [← pow_mul, ← pow_mul, mul_comm]]
          nlinarith
      _ ≤ 2 ^ (K - (4 * ℓ + 6)) := pow_le_pow_right₀ (by norm_num) hle
  have h4 : (0 : ℚ) < p ^ 4 := by positivity
  have t1 : (2 * n : ℚ) / 2 ^ (4 * ℓ + 6) ≤ 1 / (32 * p ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hp0 3]
  have t2 : (8 * n : ℚ) / 2 ^ (K - (4 * ℓ + 6)) ≤ 1 / (128 * p ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hp0 3]
  calc _ ≤ 1 / (32 * (p : ℚ) ^ 3) + 1 / (128 * p ^ 3) := add_le_add t1 t2
    _ = 5 / (128 * p ^ 3) := by field_simp; ring

/-! ## F. The per-level bounds behind the recurrence exponents

The layer recursion `F(e) ≤ a F(e/M) + C · overhead(e)` with `a = s_c/W_c ≤ M^σ` is
unrolled for `J` internal levels; the deepest internal node still has at least `d^β`
active axes, and leaves have `u < d^β` axes.  Each internal level contributes at
most `d^internal` (times the overhead's `(log p)^τ`, absorbed by `λ > internal`), and
the leaves contribute at most `d^leaf`. -/

theorem internal_level (a M e d τ' σ' β' : ℝ) (i J : ℕ) (hM : 1 < M) (ha0 : 0 ≤ a)
    (ha : a ≤ M ^ σ') (hτ : 0 ≤ τ') (hd : 1 ≤ d) (he0 : 0 < e) (he : e ≤ d)
    (hi : i + 1 ≤ J) (hdeep : d ^ β' ≤ e / M ^ (J - 1)) :
    a ^ i * (e / M ^ i) ^ τ' ≤ d ^ (τ' + (1 - β') * max (σ' - τ') 0) := by
  have hM0 : 0 < M := by linarith
  have hMi : 0 < M ^ i := pow_pos hM0 i
  have hai : a ^ i ≤ (M ^ σ') ^ i := pow_le_pow_left₀ ha0 ha i
  have hsplit : (e / M ^ i) ^ τ' = e ^ τ' / (M ^ i) ^ τ' :=
    Real.div_rpow he0.le hMi.le τ'
  have hMpow : ∀ r : ℝ, (M ^ i) ^ r = (M ^ r) ^ i := by
    intro r
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le,
      ← Real.rpow_mul hM0.le, mul_comm]
  -- a^i (e/M^i)^τ ≤ e^τ · (M^i)^(σ-τ)
  have step1 : a ^ i * (e / M ^ i) ^ τ' ≤ e ^ τ' * (M ^ i) ^ (σ' - τ') := by
    have hsplit2 : (e / M ^ i) ^ τ' = e ^ τ' / (M ^ τ') ^ i := by rw [hsplit, hMpow]
    have hdiff : (M ^ i) ^ (σ' - τ') = (M ^ σ') ^ i / (M ^ τ') ^ i := by
      rw [Real.rpow_sub hMi, hMpow, hMpow]
    have hpos : 0 < (M ^ τ') ^ i := pow_pos (Real.rpow_pos_of_pos hM0 τ') i
    rw [hsplit2, hdiff]
    calc a ^ i * (e ^ τ' / (M ^ τ') ^ i) ≤ (M ^ σ') ^ i * (e ^ τ' / (M ^ τ') ^ i) := by
          gcongr
      _ = e ^ τ' * ((M ^ σ') ^ i / (M ^ τ') ^ i) := by ring
  have heτ : e ^ τ' ≤ d ^ τ' := Real.rpow_le_rpow he0.le he hτ
  rcases le_total σ' τ' with hst | hst
  · -- `σ ≤ τ`: the levels decrease geometrically; each is at most `d^τ`
    have : (M ^ i) ^ (σ' - τ') ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ hM.le) (by linarith)
    rw [max_eq_right (by linarith), mul_zero, add_zero]
    calc _ ≤ e ^ τ' * (M ^ i) ^ (σ' - τ') := step1
      _ ≤ e ^ τ' * 1 := by gcongr
      _ ≤ d ^ τ' := by rw [mul_one]; exact heτ
  · -- `σ ≥ τ`: the deepest internal level dominates
    rw [max_eq_left (by linarith)]
    have hMJ : M ^ i ≤ M ^ (J - 1) := pow_le_pow_right₀ hM.le (by omega)
    have hdβ : 0 < d ^ β' := Real.rpow_pos_of_pos (by linarith) _
    have hMJ' : M ^ (J - 1) ≤ e / d ^ β' := by
      rw [le_div_iff₀ hdβ, mul_comm]; rwa [le_div_iff₀ (pow_pos hM0 _)] at hdeep
    have h2 : (M ^ i) ^ (σ' - τ') ≤ (e / d ^ β') ^ (σ' - τ') :=
      Real.rpow_le_rpow hMi.le (hMJ.trans hMJ') (by linarith)
    calc _ ≤ e ^ τ' * (M ^ i) ^ (σ' - τ') := step1
      _ ≤ e ^ τ' * (e / d ^ β') ^ (σ' - τ') := by gcongr
      _ = e ^ σ' * (d ^ β') ^ (-(σ' - τ')) := by
          rw [Real.div_rpow he0.le hdβ.le, Real.rpow_neg hdβ.le, div_eq_mul_inv,
            ← mul_assoc, ← Real.rpow_add he0]
          congr 2; ring
      _ ≤ d ^ σ' * (d ^ β') ^ (-(σ' - τ')) := by
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow he0.le he (le_trans hτ hst))
            (Real.rpow_nonneg hdβ.le _)
      _ = d ^ (τ' + (1 - β') * (σ' - τ')) := by
          rw [← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
          congr 1; ring

theorem leaf_level (a M u d σ' β' : ℝ) (J : ℕ) (hM : 1 < M) (ha0 : 0 ≤ a)
    (ha : a ≤ M ^ σ') (hσ0 : 0 ≤ σ') (hσ1 : σ' ≤ 1) (hd : 1 ≤ d) (hu0 : 0 < u)
    (hu : u ≤ d ^ β') (he : M ^ J * u ≤ d) :
    a ^ J * u ≤ d ^ (σ' + β' * (1 - σ')) := by
  have hM0 : 0 < M := by linarith
  have hMJ : 0 < M ^ J := pow_pos hM0 J
  have hdpos : 0 < d := by linarith
  have haJ : a ^ J ≤ (M ^ J) ^ σ' := by
    calc a ^ J ≤ (M ^ σ') ^ J := pow_le_pow_left₀ ha0 ha J
      _ = (M ^ J) ^ σ' := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le,
            ← Real.rpow_mul hM0.le, mul_comm]
  have hMJd : M ^ J ≤ d / u := by rw [le_div_iff₀ hu0]; exact he
  calc a ^ J * u ≤ (M ^ J) ^ σ' * u := by gcongr
    _ ≤ (d / u) ^ σ' * u := by gcongr
    _ = d ^ σ' * u ^ (1 - σ') := by
        rw [Real.div_rpow hdpos.le hu0.le, Real.rpow_sub hu0, Real.rpow_one]
        field_simp
    _ ≤ d ^ σ' * (d ^ β') ^ (1 - σ') := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu0.le hu (by linarith))
          (Real.rpow_nonneg hdpos.le _)
    _ = d ^ (σ' + β' * (1 - σ')) := by
        rw [← Real.rpow_mul hdpos.le, ← Real.rpow_add hdpos]

/-- with the certified parameters, `σ > τ`, so `internal = τ + (1-β)(σ-τ)` comes from
the deepest internal level, and both level bounds sit strictly below `λ < λ'` -/
theorem exponents_below_layer :
    τ < σ ∧ internal < lam ∧ leaf < lamp ∧ lam < lamp := by
  norm_num [τ, σ, internal, leaf, lam, lamp, β]

/-- the displayed comparisons of `notes/compact-control-note.tex`, lines 79-99 -/
theorem note_parameter_lines :
    1 - c = 4 / 5 ∧ max (max τ σ) internal < lam ∧ lam < lamp ∧ lamp < 1 ∧
    max leaf (1 - c) < lamp ∧ ε * C1 = 99872039 / 10 ^ 8 ∧ ε * C1 < 1 ∧
    1 / 4 + ε / 4 = 11999 / 40000 ∧ 1 / 2 + 3 * ε / 2 = 15997 / 20000 ∧
    ε < 1 / 5 ∧ (184 : ℚ) < 2 ^ 8 ∧ 1 - 2 * ε = 3001 / 5000 ∧ ε * (1 + c) < 1 := by
  norm_num [τ, σ, ε, c, lam, lamp, C1, internal, leaf, β]

/-- note line 94-95: since `ε < 1/5`, `b ≥ 2^40` implies `46 b^((1+3ε)/2) ≤ b/4`,
with `(1+3ε)/2 = 15997/20000` -/
theorem gaussian_cutoff (b : ℝ) (hb : (2 : ℝ) ^ 40 ≤ b) :
    46 * b ^ ((15997 : ℝ) / 20000) ≤ b / 4 := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hsplit : b ^ ((15997 : ℝ) / 20000) = b / b ^ ((4003 : ℝ) / 20000) := by
    rw [show (15997 : ℝ) / 20000 = 1 - 4003 / 20000 by norm_num, Real.rpow_sub hb0,
      Real.rpow_one]
  have hX : (184 : ℝ) ≤ b ^ ((4003 : ℝ) / 20000) := by
    have h1 : ((2 : ℝ) ^ 40) ^ ((4003 : ℝ) / 20000) ≤ b ^ ((4003 : ℝ) / 20000) :=
      Real.rpow_le_rpow (by positivity) hb (by norm_num)
    have h2 : ((2 : ℝ) ^ 40) ^ ((4003 : ℝ) / 20000) = (2 : ℝ) ^ ((40 : ℝ) * (4003 / 20000)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h3 : (2 : ℝ) ^ ((8 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((40 : ℝ) * (4003 / 20000)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_natCast] at h3
    norm_num at h3
    linarith
  have hXpos : 0 < b ^ ((4003 : ℝ) / 20000) := Real.rpow_pos_of_pos hb0 _
  rw [hsplit]
  calc 46 * (b / b ^ ((4003 : ℝ) / 20000)) ≤ 46 * (b / 184) := by
        gcongr
    _ = b / 4 := by ring

/-- the note's general form (lines 94-95): for every `0 ≤ ε ≤ 1/5`, `b ≥ 2^40` implies
`46 b^((1+3ε)/2) ≤ b/4`, since `(1+3ε)/2 ≤ 4/5` and `b^(1/5) ≥ 2^8 > 184` -/
theorem gaussian_cutoff_general (ε b : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 5) (hb : (2 : ℝ) ^ 40 ≤ b) :
    46 * b ^ ((1 + 3 * ε) / 2) ≤ b / 4 := by
  have hb1 : (1 : ℝ) ≤ b := le_trans (by norm_num) hb
  have hb0 : 0 < b := by linarith
  have hle : b ^ ((1 + 3 * ε) / 2) ≤ b ^ ((4 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  have hsplit : b ^ ((4 : ℝ) / 5) = b / b ^ ((1 : ℝ) / 5) := by
    rw [show (4 : ℝ) / 5 = 1 - 1 / 5 by norm_num, Real.rpow_sub hb0, Real.rpow_one]
  have hX : (184 : ℝ) ≤ b ^ ((1 : ℝ) / 5) := by
    have h1 : ((2 : ℝ) ^ 40) ^ ((1 : ℝ) / 5) ≤ b ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow (by positivity) hb (by norm_num)
    have h2 : ((2 : ℝ) ^ 40) ^ ((1 : ℝ) / 5) = 2 ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]; norm_num
    rw [h2] at h1; norm_num at h1; linarith
  have hXpos : 0 < b ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hb0 _
  calc 46 * b ^ ((1 + 3 * ε) / 2) ≤ 46 * (b / b ^ ((1 : ℝ) / 5)) := by rw [← hsplit]; gcongr
    _ ≤ 46 * (b / 184) := by gcongr
    _ = b / 4 := by ring

/-! ## G. The scoped ceiling for this complex network

Their remark that no parameters reach `2^-33` with the `h = 25` complex motif and the
retained inequalities: the Gaussian margin forces `ε < 1/5`, the leaf condition forces
`1 - λ' < (1 - β)(1 - σ)`, so `κ < g3 = ε (1 - λ') < (1 - σ)/5`; and any certified
`σ` (i.e. `s_c/W_c ≤ m^σ`) has `1 - σ ≤ η/((1 - η) log m)`. -/

theorem kappa_lt_fifth (ε' δ' β' σ' lamp' κ' : ℝ) (hδ : 0 ≤ δ') (hβ : 0 ≤ β') (hσ : σ' < 1)
    (hgauss : 0 < 1 / 4 - δ' - 5 / 4 * ε') (hleaf : σ' + β' * (1 - σ') < lamp')
    (hε : 0 < ε') (hκ : κ' < ε' * (1 - lamp')) : κ' < (1 - σ') / 5 := by
  have h1 : ε' < 1 / 5 := by linarith
  have h2 : 1 - lamp' < 1 - σ' := by nlinarith
  by_cases hl : 1 - lamp' ≤ 0
  · nlinarith
  · push_neg at hl
    calc κ' < ε' * (1 - lamp') := hκ
      _ ≤ 1 / 5 * (1 - lamp') := by gcongr
      _ ≤ 1 / 5 * (1 - σ') := by gcongr
      _ = (1 - σ') / 5 := by ring

theorem certified_saving_le (m r σ' : ℝ) (hm : 1 < m) (hr : 0 < r)
    (hcert : r ≤ m ^ σ') :
    (1 - σ') * Real.log m ≤ (1 - r / m) / (r / m) := by
  have hm0 : 0 < m := by linarith
  have hlog : Real.log r ≤ σ' * Real.log m := by
    have := Real.log_le_log hr hcert
    rwa [Real.log_rpow hm0] at this
  have hq : 0 < r / m := div_pos hr hm0
  -- `-log(r/m) ≤ 1/(r/m) - 1`
  have key : -Real.log (r / m) ≤ (1 - r / m) / (r / m) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hq)
    rw [Real.log_inv] at this
    have e : (1 - r / m) / (r / m) = (r / m)⁻¹ - 1 := by field_simp
    rw [e]; linarith
  rw [Real.log_div hr.ne' hm0.ne'] at key
  nlinarith

/-- lower bound `log 15625 > 9.655` from `log 2 > 0.6931471803` and `log y ≥ 1 - 1/y` -/
theorem log_15625_gt : (9655 : ℝ) / 1000 < Real.log 15625 := by
  have h2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hy : 1 - 16384 / 15625 ≤ Real.log ((15625 : ℝ) / 16384) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16384 / 15625 by norm_num)
    have e : Real.log ((16384 : ℝ) / 15625) = -Real.log (15625 / 16384) := by
      rw [← Real.log_inv]; norm_num
    linarith
  have hsplit : Real.log 15625 = 14 * Real.log 2 + Real.log ((15625 : ℝ) / 16384) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]; push_cast; ring
  norm_num at h2 hy ⊢; linarith

/-- every parameter choice with this complex network and the retained Gaussian and leaf
inequalities has `κ < 2^-33` -/
theorem scoped_ceiling (σ' ε' δ' β' lamp' κ' : ℝ)
    (hcert : ((sc 25 : ℕ) : ℝ) / (Wc 25 : ℕ) ≤ (15625 : ℝ) ^ σ')
    (hδ : 0 ≤ δ') (hβ : 0 ≤ β') (hσ : σ' < 1)
    (hgauss : 0 < 1 / 4 - δ' - 5 / 4 * ε') (hleaf : σ' + β' * (1 - σ') < lamp')
    (hε : 0 < ε') (hκ : κ' < ε' * (1 - lamp')) : κ' < 1 / 2 ^ 33 := by
  have hk := kappa_lt_fifth ε' δ' β' σ' lamp' κ' hδ hβ hσ hgauss hleaf hε hκ
  obtain ⟨-, -, -, hW, hs, -, -⟩ := complex25_counts
  rw [hs, hW] at hcert
  have hs := certified_saving_le 15625 ((916333630984500000 : ℝ) / 58645352620000) σ'
    (by norm_num) (by norm_num) hcert
  have hl := log_15625_gt
  have hpos : 0 < 1 - σ' := by linarith
  have : (1 - σ') * (9655 / 1000) < (1 - σ') * Real.log 15625 :=
    mul_lt_mul_of_pos_left hl hpos
  norm_num at hs this ⊢
  nlinarith

/-! ## H. Their exact ceiling value

The JSON's `scoped_ceiling.upper` is `U ≈ 8.369598074424e-11`; the true supremum
`-log(1 - η_c)/(5 log 15625)` lies below it by only about `2.6e-25` (relative), so the
check needs ~26-digit logarithms.  We use Mathlib's explicit error bound for
`-log(1 - x) = Σ x^(i+1)/(i+1)` and the identity
`log 5 = 16 log(16/15) + 12 log(25/24) + 7 log(81/80)`. -/

/-- partial sums of `-log(1 - x)` -/
noncomputable def ps (x : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)

theorem neglog_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ps x n - x ^ (n + 1) / (1 - x) ≤ -Real.log (1 - x) ∧
    -Real.log (1 - x) ≤ ps x n + x ^ (n + 1) / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg hx0]; exact hx1) n
  rw [abs_of_nonneg hx0] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  unfold ps; constructor <;> linarith

theorem log5_identity :
    Real.log 5 = 16 * -Real.log (1 - 1 / 16) + 12 * -Real.log (1 - 1 / 25) +
      7 * -Real.log (1 - 1 / 81) := by
  have e1 : -Real.log (1 - (1 : ℝ) / 16) = Real.log (16 / 15) := by
    rw [← Real.log_inv]; norm_num
  have e2 : -Real.log (1 - (1 : ℝ) / 25) = Real.log (25 / 24) := by
    rw [← Real.log_inv]; norm_num
  have e3 : -Real.log (1 - (1 : ℝ) / 81) = Real.log (81 / 80) := by
    rw [← Real.log_inv]; norm_num
  have h5 : (5 : ℝ) = (16 / 15) ^ 16 * (25 / 24) ^ 12 * (81 / 80) ^ 7 := by norm_num
  rw [e1, e2, e3]
  conv_lhs => rw [h5]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast; ring

/-- `log 15625 = 6 log 5 ≥ Llo` with errors below `10^-27` per series -/
noncomputable def Llo : ℝ :=
  6 * (16 * (ps (1 / 16) 22 - (1 / 16) ^ 23 / (1 - 1 / 16)) +
       12 * (ps (1 / 25) 20 - (1 / 25) ^ 21 / (1 - 1 / 25)) +
       7 * (ps (1 / 81) 14 - (1 / 81) ^ 15 / (1 - 1 / 81)))

theorem log_15625_ge : Llo ≤ Real.log 15625 := by
  have h5 : Real.log 15625 = 6 * Real.log 5 := by
    rw [show (15625 : ℝ) = 5 ^ 6 by norm_num, Real.log_pow]; norm_num
  have a := (neglog_bounds (1 / 16) (by norm_num) (by norm_num) 22).1
  have b := (neglog_bounds (1 / 25) (by norm_num) (by norm_num) 20).1
  have c := (neglog_bounds (1 / 81) (by norm_num) (by norm_num) 14).1
  rw [h5, log5_identity]; unfold Llo; linarith

noncomputable def ηc : ℝ := 14 / 3464399375

/-- `-log(1 - η_c) ≤ Nhi` -/
noncomputable def Nhi : ℝ := ps ηc 4 + ηc ^ 5 / (1 - ηc)

theorem neglog_eta_le : -Real.log (1 - ηc) ≤ Nhi :=
  (neglog_bounds ηc (by norm_num [ηc]) (by norm_num [ηc]) 4).2

/-- their `scoped_ceiling.upper` -/
def Uceil : ℚ := 20746540553460608247112929262864045345085076105741608893520610937226467771276028699915418386370445044824659127166650635895871722137717597479546857376527708719255663717453838247976227897533268532668858228042014619339505681211015630361605588188325457596307994168644705454015569 / 247879771154821854878830500699773260764360935854381442829251991515018712527129563362382500245253233252357075435598151081543662393578612953585247357965410441040580391962056220774007355086170004496116271962271152918875464845809694379665906644415581567011045178785707969849087514050560000

/-- the numeric core: `Nhi / (5 Llo) ≤ U` -/
theorem enclosure_le_U : Nhi / (5 * Llo) ≤ (Uceil : ℝ) := by
  have hL : 0 < Llo := by
    unfold Llo ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [div_le_iff₀ (by positivity)]
  unfold Nhi Llo ps ηc Uceil
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- negative control: the same enclosure does not fit under `U·(1 - 10⁻²⁴)`, so the
check above is tight and not passing by a wide margin -/
theorem enclosure_gt_U_shrunk : (Uceil : ℝ) * (1 - 1 / 10 ^ 24) < Nhi / (5 * Llo) := by
  have hL : 0 < Llo := by
    unfold Llo ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [lt_div_iff₀ (by positivity)]
  unfold Nhi Llo ps ηc Uceil
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `(1 - σ) log m ≤ -log(s/(W m))` for any certified `σ` -/
theorem certified_saving_log (m r σ' : ℝ) (hm : 1 < m) (hr : 0 < r)
    (hcert : r ≤ m ^ σ') : (1 - σ') * Real.log m ≤ -Real.log (r / m) := by
  have hm0 : 0 < m := by linarith
  have hlog : Real.log r ≤ σ' * Real.log m := by
    have := Real.log_le_log hr hcert
    rwa [Real.log_rpow hm0] at this
  rw [Real.log_div hr.ne' hm0.ne']; linarith

/-- **Their exact ceiling holds**: with the `h = 25` complex motif, any certified `σ`
and the retained Gaussian and leaf inequalities, `κ < U ≈ 8.3695980744e-11`. -/
theorem scoped_ceiling_exact (σ' ε' δ' β' lamp' κ' : ℝ)
    (hcert : ((sc 25 : ℕ) : ℝ) / (Wc 25 : ℕ) ≤ (15625 : ℝ) ^ σ')
    (hδ : 0 ≤ δ') (hβ : 0 ≤ β') (hσ : σ' < 1)
    (hgauss : 0 < 1 / 4 - δ' - 5 / 4 * ε') (hleaf : σ' + β' * (1 - σ') < lamp')
    (hε : 0 < ε') (hκ : κ' < ε' * (1 - lamp')) : κ' < (Uceil : ℝ) := by
  have hk := kappa_lt_fifth ε' δ' β' σ' lamp' κ' hδ hβ hσ hgauss hleaf hε hκ
  obtain ⟨-, -, -, hW, hs, -, -⟩ := complex25_counts
  rw [hs, hW] at hcert
  have hsv := certified_saving_log 15625 ((916333630984500000 : ℝ) / 58645352620000) σ'
    (by norm_num) (by norm_num) hcert
  rw [show (916333630984500000 : ℝ) / 58645352620000 / 15625 = 1 - ηc by norm_num [ηc]] at hsv
  have hL := log_15625_ge
  have hN := neglog_eta_le
  have hU := enclosure_le_U
  have hLpos : 0 < Llo := by
    unfold Llo ps; simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hpos : 0 < 1 - σ' := by linarith
  -- `(1 - σ) ≤ Nhi / Llo`
  have h1 : (1 - σ') * Llo ≤ Nhi := by
    have : (1 - σ') * Llo ≤ (1 - σ') * Real.log 15625 := mul_le_mul_of_nonneg_left hL hpos.le
    linarith
  have h2 : (1 - σ') / 5 ≤ Nhi / (5 * Llo) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  linarith

/-- the ceiling is below `8.369598075e-11` and `2^-33`, and their witness `κ = 83/10¹²` reaches over 99% of it -/
theorem ceiling_facts :
    Uceil < 8369598075 / 10 ^ 20 ∧ Uceil < 1 / 2 ^ 33 ∧ (99 : ℚ) / 100 * Uceil < 83 / 10 ^ 12 := by
  norm_num [Uceil]

/-- non-vacuity: their own witness satisfies every hypothesis of the ceiling theorem -/
theorem witness_meets_ceiling : ((83 : ℚ) / 10 ^ 12 : ℝ) < (Uceil : ℝ) := by
  have hcert := complex25_exponent
  refine scoped_ceiling_exact (1 - 418 / 10 ^ 12) (1999 / 10000) (1 / 1000000) (1 / 1000)
    (399999999833 / 400000000000) ((83 : ℚ) / 10 ^ 12 : ℝ) hcert.le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num

end KappaCheck.CrocSwap
