import PRChecksB.Common

/-!
# PR #5 (fast Gaussian resampling, κ = 1479/10¹²): certificate arithmetic

Sources, in worktree `/home/user/prs/pr5` (head `d3d370c`, base `6e56487`):
`certificates/complex-network.json` (written by `scripts/complex_network.py`) and
`certificates/fast-gaussian.json` (written by `scripts/fast_gaussian.py`); notes
`notes/complex-circuit-note.tex`, `notes/complex-circuit-construction.tex`,
`notes/fast-gaussian-note.tex`, and `patches/fast-gaussian-30.patch`.

* **A.** compressed complex network, `h = 25`, *given* `R = 108195` side roles per
  invocation and `82895` active circuit nodes (both produced by running
  `ComplexSideCircuit(25)`; taken as given): counts, `η_c = 28/205789375`,
  `log 15625 < 966/100`, `s_c/W_c < 15625^σ` with `1 - σ = 14/10⁹`, the `12 W` gate
  bound and the guard constants `E, B, C0`.
* **B.** the base witness `κ = 59/10¹¹` stored in `complex-network.json` (PR #3, on
  which #5 is stacked): 31 slacks, margins, `2^-31 < κ < 2^-30`, scoped ceiling `a/5`.
* **A′.** the retained paired bit network, `h = 50`, *given* `R = 509194` side roles
  (`paired-network.json`): counts, `η_b = 23/661055000`, and `s_b/W_b < 125000^τ` with
  `1 - τ = 296/10¹¹`; both witnesses' `τ` and `σ` are tied to these certificates
  (`exponents_certified`).
* **C.** the headline witness `κ = 1479/10¹²` of `fast-gaussian.json`: 29 slacks with
  `g5 = 1 - δ - 2ε`, margins, `min g = g3 = 147947041/10¹⁷`, `2^-30 < κ < 2^-29`,
  the guard exponent `εC1 = 980030399/10⁹`, the "next ceiling" `κ < a/2` **for τ fixed at
  `1 - a`**, the claim that the guard forces `β > 3/4`, and that with the original complex
  saving `418/10¹²` no `β` works at this `κ`.
* **D.** the ceiling for the published network: `a/2` is not a ceiling, because the same
  network certifies `1 - τ = 29643/10¹³`; every certified `τ` gives `κ < 14825/10¹³ < 2^-29`,
  and `κ = 14820/10¹³` is attained.

The analytic-parameter inequalities of the new resampling lemmas are in `PR5Analytic`.
-/

namespace PRChecksB.PR5

open Real

/-! ## A. The compressed complex network (`complex-network.json`) -/

/-- side roles per invocation, `ComplexSideCircuit(25).roles = 80595 + 27600`:
**taken as given** (produced by running the circuit) -/
def R : ℕ := 108195  -- json complex-network.json complex_counts.side_roles_per_invocation
/-- active circuit nodes (`labels.active_nodes`): **taken as given** -/
def active : ℕ := 82895  -- json complex-network.json labels.active_nodes
/-- additions / injections of the circuit: **taken as given** -/
def additions : ℕ := 80595  -- json complex-network.json circuit.additions
def injections : ℕ := 27600  -- json complex-network.json circuit.injections

def v : ℕ := Nat.choose 25 3
def m : ℕ := 25 ^ 3  -- json complex-network.json complex_counts.m
def N : ℕ := v ^ 3
def I : ℕ := 3 * v ^ 2
/-- `W = 2N + I(R + h + 1)` (`scripts/complex_network.py`, `counts`) -/
def W : ℕ := 2 * N + I * (R + 25 + 1)
/-- `L = I (h + 1) h` -/
def L : ℕ := I * (25 + 1) * 25
/-- `s = W m - 2N + 2L`, written so that ℕ subtraction is harmless -/
def s : ℕ := W * m + 2 * L - 2 * N

/-- the certified complex saving `a_c = 14/10⁹` -/
def aC : ℚ := 7 / 500000000  -- json complex-network.json complex_saving

theorem v_eq : v = 2300 := by decide
theorem c22 : Nat.choose 22 3 = 1540 := by decide

theorem counts :
    v = 2300 ∧  -- json complex-network.json complex_counts.v
    m = 15625 ∧  -- json complex-network.json complex_counts.m
    N = 12167000000 ∧  -- json complex-network.json complex_counts.N
    I = 15870000 ∧  -- json complex-network.json complex_counts.I
    W = 1741801270000 ∧  -- json complex-network.json complex_counts.W
    L = 10315500000 ∧  -- json complex-network.json complex_counts.L
    s = 27215641140750000 ∧  -- json complex-network.json complex_counts.s
    W * m - s = 3703000000 ∧  -- json complex-network.json complex_counts.deficit
    2 * N ≤ W * m ∧ L < N ∧
    R = additions + injections ∧
    v * (Nat.choose 22 3 + 3 * 22) = 3693800  -- json complex-network.json complex_counts.original_side_wires_per_invocation
    := by
  simp only [W, L, s, N, I, m, R, additions, injections, v_eq, c22]
  norm_num

/-- the ℕ form of `s` is the script's `W m - 2N + 2L` -/
theorem s_eq : (s : ℤ) = (W : ℤ) * m - 2 * N + 2 * L := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := counts
  unfold s; push_cast [show 2 * N ≤ W * m + 2 * L by omega]; ring

theorem eta :
    ((W * m - s : ℕ) : ℚ) / (W * m) = 28 / 205789375  -- json complex-network.json complex_counts.eta
    := by
  simp only [W, L, s, N, I, m, R, v_eq]; norm_num

/-- `η_c - a_c (966/100)` is the certificate's `complex_deficit_slack` -/
theorem deficit_slack :
    (28 / 205789375 : ℚ) - aC * (966 / 100) =
      6761797 / 8231575000000000  -- json complex-network.json complex_deficit_slack
    := by norm_num [aC]

/-- `log m < 483/50 = 966/100` -/
theorem log_m : Real.log 15625 < 483 / 50  -- json complex-network.json log_m_upper
    := by
  linarith [log_15625_note]

/-- the certificate's rational log enclosure (`log_integer_bounds`) -/
def encLo : ℚ :=
  1003674733095412338935264801206694829502804118660273821722358572561777951813562324984581151664909098376456139346987946438356114944865114544057566309229396051200891281693308045036569381219925884240815457348697380244265196736 / 103936362434495646010619550865033734742948881177937982419226476521510946436948314218071351858470876811875561920539687733866419026027866373569756270393100104240876895441796280524990301784985328254889750901950661699188332905  -- json complex-network.json log_enclosure.0
def encHi : ℚ :=
  119905674780465260758132999318298249674205865631153226854493684575647168973933813765866273005815485563618924127097549911779010579460799218169313950759672923946122257420539013677630274686709038285230521425787947340179037163618384721 / 12416930765507746510068682343342696843957626338057657633016923061769841067667425271918924168691987416458733797440474694605908192976129102762466882436295692453310093108779928980052174719912913882184162241086372384329699504384000000  -- json complex-network.json log_enclosure.1

/-- the enclosure contains `log 15625 = 96A + 72B + 42C` (`A = -log(15/16)`, …, series to
`10⁻²⁷`), and its upper end is below the stated bound -/
theorem log_enclosure_hi_lt :
    (encLo : ℝ) < Real.log 15625 ∧ Real.log 15625 < encHi ∧ encHi < 483 / 50 := by
  have h := log_prod 96 72 42 15625 (by norm_num)
  have a := neglog_bounds (1 / 16) (by norm_num) (by norm_num) 24
  have b := neglog_bounds (1 / 25) (by norm_num) (by norm_num) 21
  have c := neglog_bounds (1 / 81) (by norm_num) (by norm_num) 15
  unfold ps at a b c
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at a b c
  norm_num at a b c h
  rw [h]
  refine ⟨?_, ?_, by norm_num [encHi]⟩
  · unfold encLo; push_cast; linarith [a.1, b.1, c.1]
  · unfold encHi; push_cast; linarith [a.2, b.2, c.2]

/-- **exponent certificate**: `s_c / W_c < 15625 ^ (1 - a_c)`, `a_c = 14/10⁹` -/
theorem complex_exponent :
    ((s : ℕ) : ℝ) / (W : ℕ) < (15625 : ℝ) ^ (1 - (aC : ℝ)) := by
  obtain ⟨-, -, -, -, hW, -, hs, -⟩ := counts
  rw [hs, hW, show ((aC : ℚ) : ℝ) = 14 / 10 ^ 9 by norm_num [aC]]
  apply exponent_certificate 15625 (966 / 100) (14 / 10 ^ 9) (28 / 205789375) _
    (by norm_num) (by norm_num) log_15625_note
  · norm_num
  · norm_num

/-- the gate bound behind `E = 64(W+m+1)^3`: `I (4·active + 4v + 4) ≤ 12 W` -/
theorem gates :
    4 * active + 4 * v + 4 = 340784 ∧  -- json complex-network.json gates.gates_per_invocation
    I * (4 * active + 4 * v + 4) = 5408242080000 ∧  -- json complex-network.json gates.total_gates
    12 * W = 20901615240000 ∧  -- json complex-network.json gates.twelve_W
    I * (4 * active + 4 * v + 4) ≤ 12 * W := by
  simp only [W, N, I, R, active, v_eq]; norm_num

/-! ### Guard constants (`scripts/complex_network.py`, `guard`) -/

def Eg : ℕ := 64 * (W + m + 1) ^ 3
def Bg : ℕ := s + Eg
def C0n : ℕ :=
  321727027889740762489223803495350305328695729120143793284991524019954162292886152000000  -- json complex-network.json witness.guard.C0
def ζ : ℚ := 1 / 10000  -- json complex-network.json witness.guard.zeta

theorem guard_constants :
    Eg = 338201706233372774319082463160146840064 ∧  -- json complex-network.json witness.guard.E
    Bg = 338201706233372774319109678801287590064 ∧  -- json complex-network.json witness.guard.B
    m = 15625 ∧  -- json complex-network.json witness.guard.m
    s = 27215641140750000 ∧  -- json complex-network.json witness.guard.s
    3 ≤ m ∧ 2 ≤ s ∧ s < m ^ 5 ∧ s * (8 + Eg) ≤ 9 * Bg ^ 2 ∧
    (C0n : ℚ) = max (128 * 15625 * (Bg : ℚ) ^ 2) (18 * 15625 * (Bg : ℚ) ^ 2 * (1 + 1 / ζ)) ∧
    9 * 15625 * (Bg : ℚ) ^ 2 * (1 + 1 / ζ) + 18 ≤ C0n := by
  simp only [Eg, Bg, C0n, ζ, W, L, s, N, I, m, R, v_eq]
  norm_num

/-- `fast-gaussian.json` repeats the complex counts and guard -/
theorem fast_gaussian_repeats :
    W = 1741801270000 ∧  -- json fast-gaussian.json complex_counts.W
    s = 27215641140750000 ∧  -- json fast-gaussian.json complex_counts.s
    ((W * m - s : ℕ) : ℚ) / (W * m) = 28 / 205789375 ∧  -- json fast-gaussian.json complex_counts.eta
    Eg = 338201706233372774319082463160146840064 ∧  -- json fast-gaussian.json witness.guard.E
    Bg = 338201706233372774319109678801287590064 ∧  -- json fast-gaussian.json witness.guard.B
    C0n = 321727027889740762489223803495350305328695729120143793284991524019954162292886152000000 ∧  -- json fast-gaussian.json witness.guard.C0
    m = 15625 ∧  -- json fast-gaussian.json witness.guard.m
    s = 27215641140750000  -- json fast-gaussian.json witness.guard.s
    := by
  refine ⟨counts.2.2.2.2.1, counts.2.2.2.2.2.2.1, eta, guard_constants.1, guard_constants.2.1, rfl,
    counts.2.1, counts.2.2.2.2.2.2.1⟩

/-- the note's "33.49 times the previous complex saving 418/10¹²" -/
theorem saving_ratio : (3349 : ℚ) / 100 < (14 / 10 ^ 9) / (418 / 10 ^ 12) ∧
    (14 / 10 ^ 9) / (418 / 10 ^ 12) < (3350 : ℚ) / 100 := by norm_num

/-! ## A′. The retained paired bit network, `h = 50` (`paired-network.json`) -/

/-- side roles per invocation of `SharedPointCircuit(50, PairedExclusionCircuit(49))`:
**taken as given** (produced by running the circuit) -/
def R50 : ℕ := 509194  -- json paired-network.json bit_counts.side_roles_per_invocation
def hb : ℕ := 50  -- json paired-network.json bit_counts.h
def vb : ℕ := Nat.choose hb 3
def mb : ℕ := hb ^ 3
def Nb : ℕ := vb ^ 3
/-- `W_b = 2N + 2v²(R + h)` -/
def Wb : ℕ := 2 * Nb + 2 * vb ^ 2 * (R50 + hb)
/-- `L_b = 3v²h²` -/
def Lb : ℕ := 3 * vb ^ 2 * hb ^ 2
def Db : ℕ := Nb - 2 * Lb
def sb : ℕ := Wb * mb - Db
/-- the certified bit saving `a = 296/10¹¹` -/
def aB : ℚ := 37 / 12500000000  -- json paired-network.json bit_saving

theorem bit_counts :
    vb = 19600 ∧  -- json paired-network.json bit_counts.v
    mb = 125000 ∧  -- json paired-network.json bit_counts.m
    Nb = 7529536000000 ∧  -- json paired-network.json bit_counts.N
    Wb = 406321422080000 ∧  -- json paired-network.json bit_counts.W
    Lb = 2881200000000 ∧  -- json paired-network.json bit_counts.L
    Db = 1767136000000 ∧  -- json paired-network.json bit_counts.D
    sb = 50790175992864000000  -- json paired-network.json bit_counts.s
    := by
  simp only [Wb, Lb, Db, sb, Nb, mb, vb, R50, hb]; norm_num [Nat.choose]

theorem bit_eta :
    ((Db : ℕ) : ℚ) / (Wb * mb) = 23 / 661055000  -- json paired-network.json bit_counts.eta
    := by
  simp only [Wb, Lb, Db, Nb, mb, vb, R50, hb]; norm_num [Nat.choose]

theorem bit_deficit_slack :
    (23 / 661055000 : ℚ) - aB * (11737 / 1000) =
      84861241 / 1652637500000000000  -- json paired-network.json bit_deficit_slack
    := by norm_num [aB]

theorem bit_log : Real.log 125000 < 11737 / 1000  -- json paired-network.json log_m_upper
    := log_125000

/-- **exponent certificate**: `s_b / W_b < 125000 ^ (1 - a)`, `a = 296/10¹¹` -/
theorem bit_exponent :
    ((sb : ℕ) : ℝ) / (Wb : ℕ) < (125000 : ℝ) ^ (1 - (aB : ℝ)) := by
  obtain ⟨-, -, -, hW, -, -, hs⟩ := bit_counts
  rw [hs, hW, show ((aB : ℚ) : ℝ) = 296 / 10 ^ 11 by norm_num [aB]]
  apply exponent_certificate 125000 (11737 / 1000) (296 / 10 ^ 11) (23 / 661055000) _
    (by norm_num) (by norm_num) log_125000
  · norm_num
  · norm_num

/-- the same network certifies every `τ` with `(1 - τ) · 11737/1000 ≤ η_b`; here
`1 - τ = 29643/10¹³` (used in section D) -/
theorem bit_exponent_29643 :
    ((sb : ℕ) : ℝ) / (Wb : ℕ) < (125000 : ℝ) ^ (1 - (29643 / 10 ^ 13 : ℝ)) := by
  obtain ⟨-, -, -, hW, -, -, hs⟩ := bit_counts
  rw [hs, hW]
  apply exponent_certificate 125000 (11737 / 1000) (29643 / 10 ^ 13) (23 / 661055000) _
    (by norm_num) (by norm_num) log_125000
  · norm_num
  · norm_num

/-! ## B. The base witness κ = 59/10¹¹ (`complex-network.json`, tight Gaussian) -/

namespace Base59

def P : Params where
  τ := 12499999963 / 12500000000  -- json complex-network.json witness.parameters.tau
  σ := 499999993 / 500000000  -- json complex-network.json witness.parameters.sigma
  ε := 19999 / 100000  -- json complex-network.json witness.parameters.epsilon
  c := 999 / 1000  -- json complex-network.json witness.parameters.c
  lam := 499999998521 / 500000000000  -- json complex-network.json witness.parameters.lam
  lamp := 249999999261 / 250000000000  -- json complex-network.json witness.parameters.lamp
  κ := 59 / 100000000000  -- json complex-network.json witness.parameters.kappa
  β := 1 / 1000  -- json complex-network.json witness.parameters.beta
  δ := 1 / 1000000  -- json complex-network.json witness.parameters.delta
  C1 := 49961 / 10000  -- json complex-network.json witness.parameters.C1

/-- the parameters are those of `notes/complex-circuit-note.tex` lines 50-59 -/
theorem parameter_origin :
    P.τ = 1 - 296 / 10 ^ 11 ∧ P.σ = 1 - 14 / 10 ^ 9 ∧ P.lam = 1 - 2958 / 10 ^ 12 ∧
    P.lamp = 1 - 2956 / 10 ^ 12 ∧ P.κ = 59 / 10 ^ 11 ∧ P.C1 = 5 - 4 * P.β + ζ ∧
    P.β = 1 / 1000 ∧  -- json complex-network.json witness.guard.beta
    P.C1 = 49961 / 10000 ∧  -- json complex-network.json witness.guard.C1
    1 - P.τ = 37 / 12500000000  -- json complex-network.json bit_saving
    ∧ 1 - P.σ = 7 / 500000000  -- json complex-network.json complex_saving
    ∧ 1 - P.τ = aB ∧ 1 - P.σ = aC
    := by
  norm_num [P, ζ, aB, aC]

/-- `τ` and `σ` are the exponents certified by the two retained networks -/
theorem exponents_certified :
    ((sb : ℕ) : ℝ) / (Wb : ℕ) < (125000 : ℝ) ^ ((P.τ : ℚ) : ℝ) ∧
    ((s : ℕ) : ℝ) / (W : ℕ) < (15625 : ℝ) ^ ((P.σ : ℚ) : ℝ) := by
  have hτ : ((P.τ : ℚ) : ℝ) = 1 - (aB : ℝ) := by
    rw [show P.τ = 1 - aB by norm_num [P, aB]]; push_cast; ring
  have hσ : ((P.σ : ℚ) : ℝ) = 1 - (aC : ℝ) := by
    rw [show P.σ = 1 - aC by norm_num [P, aC]]; push_cast; ring
  rw [hτ, hσ]; exact ⟨bit_exponent, complex_exponent⟩

theorem recurrence_values :
    P.internal = 12499999963 / 12500000000 ∧  -- json complex-network.json witness.recurrence.internal
    P.leaf = 499999993007 / 500000000000 ∧  -- json complex-network.json witness.recurrence.leaf
    P.prep = 1 / 1000 ∧  -- json complex-network.json witness.recurrence.preprocessing
    P.layer = 12499999963 / 12500000000  -- json complex-network.json witness.recurrence.layer
    := by
  norm_num [P, Params.internal, Params.leaf, Params.prep, Params.layer]

/-- all 31 constraint slacks of `constraints(…, 'nonadjacent', 'tight-gaussian')`
with the compact-control `packed_overhead` and `reserved_axes`, at their exact values -/
theorem slack_values :
    P.ε * P.c = 19979001 / 100000000 ∧  -- json complex-network.json witness.constraint_slacks.K_dominates_log_p
    1 - P.ε - P.ε * P.c = 60021999 / 100000000 ∧  -- json complex-network.json witness.constraint_slacks.K_smaller_than_ell
    1 / 4 - P.ε / 4 = 80001 / 400000 ∧  -- json complex-network.json witness.constraint_slacks.alpha_below_sqrt_p
    1 - P.β = 999 / 1000 ∧  -- json complex-network.json witness.constraint_slacks.beta_below_one
    P.β = 1 / 1000 ∧  -- json complex-network.json witness.constraint_slacks.beta_positive
    P.c = 999 / 1000 ∧  -- json complex-network.json witness.constraint_slacks.c_positive
    1 - P.τ - P.ε * (1 - P.τ) = 2960037 / 1250000000000000 ∧  -- json complex-network.json witness.constraint_slacks.crt_layout
    1 / 8 - P.δ = 124999 / 1000000 ∧  -- json complex-network.json witness.constraint_slacks.delta_below_one_eighth
    P.δ = 1 / 1000000 ∧  -- json complex-network.json witness.constraint_slacks.delta_positive
    1 / 3 - P.ε = 40003 / 300000 ∧  -- json complex-network.json witness.constraint_slacks.dimension_upper_bound
    P.ε = 19999 / 100000 ∧  -- json complex-network.json witness.constraint_slacks.epsilon_positive
    1 / 2 - 3 / 2 * P.ε = 40003 / 200000 ∧  -- json complex-network.json witness.constraint_slacks.gamma_sublinear
    1 / 4 - P.δ - 5 / 4 * P.ε = 23 / 2000000 ∧  -- json complex-network.json witness.constraint_slacks.gaussian_cost
    1 - P.ε * P.C1 = 829961 / 1000000000 ∧  -- json complex-network.json witness.constraint_slacks.guard_width
    P.κ = 59 / 100000000000 ∧  -- json complex-network.json witness.constraint_slacks.kappa_positive
    P.lam - P.σ = 5521 / 500000000000 ∧  -- json complex-network.json witness.constraint_slacks.lambda_above_sigma
    P.lam - P.τ = 1 / 500000000000 ∧  -- json complex-network.json witness.constraint_slacks.lambda_above_tau
    1 - P.lam = 1479 / 500000000000 ∧  -- json complex-network.json witness.constraint_slacks.lambda_below_one
    P.lamp - P.lam = 1 / 500000000000 ∧  -- json complex-network.json witness.constraint_slacks.lambda_prime_above_lambda
    1 - P.lamp = 739 / 250000000000 ∧  -- json complex-network.json witness.constraint_slacks.lambda_prime_below_one
    P.lamp - (P.σ + P.β * (1 - P.σ)) = 1103 / 100000000000 ∧  -- json complex-network.json witness.constraint_slacks.leaf_cost
    P.lam - P.internal = 1 / 500000000000 ∧  -- json complex-network.json witness.constraint_slacks.packed_overhead
    1 - P.ε * (1 + P.c) = 60021999 / 100000000 ∧  -- json complex-network.json witness.constraint_slacks.prefix_cost
    1 - 2 * P.ε = 30001 / 50000 ∧  -- json complex-network.json witness.constraint_slacks.prime_interval_growth
    1 - P.ε = 80001 / 100000 ∧  -- json complex-network.json witness.constraint_slacks.r_superpolynomial
    P.lamp - P.prep = 249749999261 / 250000000000 ∧  -- json complex-network.json witness.constraint_slacks.reserved_axes
    1 - P.δ - P.ε = 800009 / 1000000 ∧  -- json complex-network.json witness.constraint_slacks.scalar_cost
    1 - P.σ = 7 / 500000000 ∧  -- json complex-network.json witness.constraint_slacks.sigma_below_one
    P.σ = 499999993 / 500000000 ∧  -- json complex-network.json witness.constraint_slacks.sigma_positive
    1 - P.τ = 37 / 12500000000 ∧  -- json complex-network.json witness.constraint_slacks.tau_below_one
    P.τ = 12499999963 / 12500000000  -- json complex-network.json witness.constraint_slacks.tau_positive
    := by
  norm_num [P, Params.internal, Params.prep]

theorem constraint_slacks :
    0 < P.ε * P.c ∧  -- K_dominates_log_p
    0 < 1 - P.ε - P.ε * P.c ∧  -- K_smaller_than_ell
    0 < 1 / 4 - P.ε / 4 ∧  -- alpha_below_sqrt_p
    0 < 1 - P.β ∧  -- beta_below_one
    0 < P.β ∧  -- beta_positive
    0 < P.c ∧  -- c_positive
    0 < 1 - P.τ - P.ε * (1 - P.τ) ∧  -- crt_layout
    0 < 1 / 8 - P.δ ∧  -- delta_below_one_eighth
    0 < P.δ ∧  -- delta_positive
    0 < 1 / 3 - P.ε ∧  -- dimension_upper_bound
    0 < P.ε ∧  -- epsilon_positive
    0 < 1 / 2 - 3 / 2 * P.ε ∧  -- gamma_sublinear
    0 < 1 / 4 - P.δ - 5 / 4 * P.ε ∧  -- gaussian_cost
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
    P.g1 = 60021999 / 100000000 ∧  -- json complex-network.json witness.margins.g1
    P.g2 = 739223037 / 1250000000000000000 ∧  -- json complex-network.json witness.margins.g2
    P.g3 = 14779261 / 25000000000000000 ∧  -- json complex-network.json witness.margins.g3
    P.g4 = 2960037 / 1250000000000000 ∧  -- json complex-network.json witness.margins.g4
    P.g5tight = 23 / 2000000 ∧  -- json complex-network.json witness.margins.g5
    P.g6 = 800009 / 1000000 ∧  -- json complex-network.json witness.margins.g6
    P.g7 = 19999 / 100000  -- json complex-network.json witness.margins.g7
    := by
  norm_num [P, Params.g1, Params.g2, Params.g3, Params.g4, Params.g5tight, Params.g6, Params.g7]

/-- `g3` is the minimum margin, the gap is `29261/(25·10¹⁵)`, and `2^-31 < κ < 2^-30` -/
theorem kappa_witness :
    P.g3 ≤ P.g1 ∧ P.g3 ≤ P.g2 ∧ P.g3 ≤ P.g4 ∧ P.g3 ≤ P.g5tight ∧ P.g3 ≤ P.g6 ∧ P.g3 ≤ P.g7 ∧
    P.g3 = 14779261 / 25000000000000000 ∧  -- json complex-network.json witness.minimum_margin
    P.g3 - P.κ = 29261 / 25000000000000000 ∧  -- json complex-network.json witness.absorption_gap
    P.κ < P.g3 ∧ (1 : ℚ) / 2 ^ 31 < P.κ ∧ P.κ < 1 / 2 ^ 30 := by
  norm_num [P, Params.g1, Params.g2, Params.g3, Params.g4, Params.g5tight, Params.g6, Params.g7]

/-- the displayed lines of `notes/complex-circuit-note.tex` 60-78 and 105-107 -/
theorem note_lines :
    P.σ < P.τ ∧ P.internal = P.τ ∧ max (max P.τ P.σ) P.internal < P.lam ∧ P.lam < P.lamp ∧
    P.lamp < 1 ∧ max P.leaf (1 - P.c) < P.lamp ∧
    P.ε * P.C1 = 999170039 / 10 ^ 9 ∧ P.ε * P.C1 < 1 ∧ P.ε * (1 + P.c) < 1 ∧
    1 / 4 + P.ε / 4 = 119999 / 400000 ∧ 1 / 2 + 3 * P.ε / 2 = 159997 / 200000 ∧
    1 - 2 * P.ε = 30001 / 50000 ∧ P.ε < 1 / 5 ∧
    (296 : ℚ) / (5 * 10 ^ 11) = 37 / 62500000000 ∧
    (296 : ℚ) / (5 * 10 ^ 11) < 1 / 2 ^ 30 ∧
    996 / 1000 * ((296 : ℚ) / (5 * 10 ^ 11)) < P.κ ∧
    P.κ / (83 / 10 ^ 12) = 590 / 83  -- json complex-network.json improvement_over_compact_control
    := by
  norm_num [P, Params.internal, Params.leaf]

/-- the stated ceiling `κ < a/5 = 37/62500000000 < 2^-30` with the retained Gaussian margin,
**for τ fixed at `P.τ = 1 - a`** (a larger certified `1 - τ` raises it: README finding #1) -/
theorem scoped_ceiling (ε' δ' lamp' κ' : ℝ) (hδ : 0 ≤ δ')
    (hgauss : 0 < 1 / 4 - δ' - 5 / 4 * ε') (hl : ((P.τ : ℚ) : ℝ) < lamp')
    (hε : 0 < ε') (h3 : κ' < ε' * (1 - lamp')) :
    κ' < 37 / 62500000000 := by  -- json complex-network.json scoped_ceiling.upper
  have hτ : ((P.τ : ℚ) : ℝ) = 1 - 296 / 10 ^ 11 := by norm_num [P]
  rw [hτ] at hl
  have := ceiling_fifth (1 - 296 / 10 ^ 11) ε' δ' lamp' κ' (by norm_num) hδ hgauss hl hε h3
  linarith

end Base59

/-! ## C. The headline witness κ = 1479/10¹² (`fast-gaussian.json`) -/

namespace Fast

def P : Params where
  τ := 12499999963 / 12500000000  -- json fast-gaussian.json witness.parameters.tau
  σ := 499999993 / 500000000  -- json fast-gaussian.json witness.parameters.sigma
  ε := 49999 / 100000  -- json fast-gaussian.json witness.parameters.epsilon
  c := 9999 / 10000  -- json fast-gaussian.json witness.parameters.c
  lam := 1999999994081 / 2000000000000  -- json fast-gaussian.json witness.parameters.lam
  lamp := 999999997041 / 1000000000000  -- json fast-gaussian.json witness.parameters.lamp
  κ := 1479 / 1000000000000  -- json fast-gaussian.json witness.parameters.kappa
  β := 19 / 25  -- json fast-gaussian.json witness.parameters.beta
  δ := 1 / 1000000  -- json fast-gaussian.json witness.parameters.delta
  C1 := 19601 / 10000  -- json fast-gaussian.json witness.parameters.C1

/-- the parameters of `notes/fast-gaussian-note.tex` lines 133-142 -/
theorem parameter_origin :
    P.τ = 1 - 296 / 10 ^ 11 ∧ P.σ = 1 - 14 / 10 ^ 9 ∧ P.lam = 1 - 29595 / 10 ^ 13 ∧
    P.lamp = 1 - 2959 / 10 ^ 12 ∧ P.κ = 1479 / 10 ^ 12 ∧
    P.C1 = 5 - 4 * P.β + ζ ∧ ζ = 1 / 10000 ∧  -- json fast-gaussian.json witness.guard.zeta
    P.β = 19 / 25 ∧  -- json fast-gaussian.json witness.guard.beta
    P.C1 = 19601 / 10000 ∧  -- json fast-gaussian.json witness.guard.C1
    1 - P.τ = 37 / 12500000000 ∧  -- json fast-gaussian.json bit_saving
    1 - P.σ = 7 / 500000000 ∧  -- json fast-gaussian.json complex_saving
    1 - P.τ = aB ∧ 1 - P.σ = aC
    := by
  norm_num [P, ζ, aB, aC]

/-- `τ` and `σ` are the exponents certified by the two retained networks -/
theorem exponents_certified :
    ((sb : ℕ) : ℝ) / (Wb : ℕ) < (125000 : ℝ) ^ ((P.τ : ℚ) : ℝ) ∧
    ((s : ℕ) : ℝ) / (W : ℕ) < (15625 : ℝ) ^ ((P.σ : ℚ) : ℝ) := by
  have hτ : ((P.τ : ℚ) : ℝ) = 1 - (aB : ℝ) := by
    rw [show P.τ = 1 - aB by norm_num [P, aB]]; push_cast; ring
  have hσ : ((P.σ : ℚ) : ℝ) = 1 - (aC : ℝ) := by
    rw [show P.σ = 1 - aC by norm_num [P, aC]]; push_cast; ring
  rw [hτ, hσ]; exact ⟨bit_exponent, complex_exponent⟩

/-- the 29 slacks in `Params.FastOK` form, and `κ` below every margin -/
theorem fast_ok : P.FastOK ∧ P.FastAbsorbs := by
  unfold Params.FastOK Params.FastAbsorbs
  norm_num [P, Params.internal, Params.prep, Params.g1, Params.g2, Params.g3, Params.g4,
    Params.g5fast, Params.g6, Params.g7]

theorem recurrence_values :
    P.internal = 12499999963 / 12500000000 ∧  -- json fast-gaussian.json witness.recurrence.internal
    P.leaf = 6249999979 / 6250000000 ∧  -- json fast-gaussian.json witness.recurrence.leaf
    P.prep = 1 / 10000 ∧  -- json fast-gaussian.json witness.recurrence.preprocessing
    P.layer = 12499999963 / 12500000000  -- json fast-gaussian.json witness.recurrence.layer
    := by
  norm_num [P, Params.internal, Params.leaf, Params.prep, Params.layer]

/-- all 29 slacks of `fast_constraints` (`gaussian_cost = 1 - δ - 2ε`,
`alpha_squared_theta_growth = 1 - 2ε`, four retained-Gaussian rows removed) plus the
compact-control `packed_overhead` and `reserved_axes`, at their exact values -/
theorem slack_values :
    P.ε * P.c = 499940001 / 1000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.K_dominates_log_p
    1 - P.ε - P.ε * P.c = 69999 / 1000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.K_smaller_than_ell
    1 - 2 * P.ε = 1 / 50000 ∧  -- json fast-gaussian.json witness.constraint_slacks.alpha_squared_theta_growth
    1 - P.β = 6 / 25 ∧  -- json fast-gaussian.json witness.constraint_slacks.beta_below_one
    P.β = 19 / 25 ∧  -- json fast-gaussian.json witness.constraint_slacks.beta_positive
    P.c = 9999 / 10000 ∧  -- json fast-gaussian.json witness.constraint_slacks.c_positive
    1 - P.τ - P.ε * (1 - P.τ) = 1850037 / 1250000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.crt_layout
    1 / 8 - P.δ = 124999 / 1000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.delta_below_one_eighth
    P.δ = 1 / 1000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.delta_positive
    P.ε = 49999 / 100000 ∧  -- json fast-gaussian.json witness.constraint_slacks.epsilon_positive
    1 - P.δ - 2 * P.ε = 19 / 1000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.gaussian_cost
    1 - P.ε * P.C1 = 19969601 / 1000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.guard_width
    P.κ = 1479 / 1000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.kappa_positive
    P.lam - P.σ = 22081 / 2000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.lambda_above_sigma
    P.lam - P.τ = 1 / 2000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.lambda_above_tau
    1 - P.lam = 5919 / 2000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.lambda_below_one
    P.lamp - P.lam = 1 / 2000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.lambda_prime_above_lambda
    1 - P.lamp = 2959 / 1000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.lambda_prime_below_one
    P.lamp - (P.σ + P.β * (1 - P.σ)) = 401 / 1000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.leaf_cost
    P.lam - P.internal = 1 / 2000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.packed_overhead
    1 - P.ε * (1 + P.c) = 69999 / 1000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.prefix_cost
    1 - 2 * P.ε = 1 / 50000 ∧  -- json fast-gaussian.json witness.constraint_slacks.prime_interval_growth
    1 - P.ε = 50001 / 100000 ∧  -- json fast-gaussian.json witness.constraint_slacks.r_superpolynomial
    P.lamp - P.prep = 999899997041 / 1000000000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.reserved_axes
    1 - P.δ - P.ε = 500009 / 1000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.scalar_cost
    1 - P.σ = 7 / 500000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.sigma_below_one
    P.σ = 499999993 / 500000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.sigma_positive
    1 - P.τ = 37 / 12500000000 ∧  -- json fast-gaussian.json witness.constraint_slacks.tau_below_one
    P.τ = 12499999963 / 12500000000  -- json fast-gaussian.json witness.constraint_slacks.tau_positive
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
    P.g1 = 69999 / 1000000000 ∧  -- json fast-gaussian.json witness.margins.g1
    P.g2 = 18497780037 / 12500000000000000000 ∧  -- json fast-gaussian.json witness.margins.g2
    P.g3 = 147947041 / 100000000000000000 ∧  -- json fast-gaussian.json witness.margins.g3
    P.g4 = 1850037 / 1250000000000000 ∧  -- json fast-gaussian.json witness.margins.g4
    P.g5fast = 19 / 1000000 ∧  -- json fast-gaussian.json witness.margins.g5
    P.g6 = 500009 / 1000000 ∧  -- json fast-gaussian.json witness.margins.g6
    P.g7 = 49999 / 100000  -- json fast-gaussian.json witness.margins.g7
    := by
  norm_num [P, Params.g1, Params.g2, Params.g3, Params.g4, Params.g5fast, Params.g6, Params.g7]

/-- **headline**: `g3` is the minimum margin `147947041/10¹⁷`, it exceeds `κ = 1479/10¹²`
by `47041/10¹⁷`, and `2^-30 < κ < 2^-29` -/
theorem kappa_witness :
    P.g3 ≤ P.g1 ∧ P.g3 ≤ P.g2 ∧ P.g3 ≤ P.g4 ∧ P.g3 ≤ P.g5fast ∧ P.g3 ≤ P.g6 ∧ P.g3 ≤ P.g7 ∧
    P.g3 = 147947041 / 100000000000000000 ∧  -- json fast-gaussian.json witness.minimum_margin
    P.g3 - P.κ = 47041 / 100000000000000000 ∧  -- json fast-gaussian.json witness.absorption_gap
    P.κ < P.g3 ∧ (1 : ℚ) / 2 ^ 30 < P.κ ∧ P.κ < 1 / 2 ^ 29 := by
  norm_num [P, Params.g1, Params.g2, Params.g3, Params.g4, Params.g5fast, Params.g6, Params.g7]

/-- the displayed comparisons of `notes/fast-gaussian-note.tex` 143-180 and the exponents
of `patches/fast-gaussian-30.patch` (α, K, ℓ, prime ratio, guard) -/
theorem note_lines :
    P.σ < P.τ ∧ P.internal = P.τ ∧ max (max P.τ P.σ) P.internal < P.lam ∧ P.lam < P.lamp ∧
    P.lamp < 1 ∧ max (P.σ + P.β * (1 - P.σ)) (1 - P.c) < P.lamp ∧
    P.ε * P.C1 = 980030399 / 10 ^ 9 ∧ P.ε * P.C1 < 1 ∧
    P.ε * (1 + P.c) < 1 ∧ 1 - 2 * P.ε > 0 ∧ P.ε + P.δ < 1 ∧
    (47 : ℚ) / 10 < (14 / 10 ^ 9) / (296 / 10 ^ 11) ∧
    (1 - P.ε) / 2 = 50001 / 200000 ∧ P.ε * P.c = 499940001 / 10 ^ 9 ∧
    1 - P.ε = 50001 / 100000 ∧ 1 - 2 * P.ε = 1 / 50000 ∧
    P.κ / (59 / 10 ^ 11) = 1479 / 590 ∧  -- json fast-gaussian.json improvement_over_compressed_complex
    P.κ / (83 / 10 ^ 12) = 1479 / 83  -- json fast-gaussian.json improvement_over_compact_control
    := by
  norm_num [P, Params.internal]

/-- "The next ceiling": `a/2 = 37/25000000000 < 2^-29`, and the witness exceeds 99.9% of it -/
theorem ceiling_values :
    (296 : ℚ) / 10 ^ 11 / 2 = 37 / 25000000000 ∧
    (296 : ℚ) / 10 ^ 11 / 2 < 1 / 2 ^ 29 ∧ 999 / 1000 * ((296 : ℚ) / 10 ^ 11 / 2) < P.κ := by
  norm_num [P]

/-- the stated ceiling `κ < a/2 = 37/25000000000`, from `g3` and `g4` alone, **for τ fixed at
`P.τ = 1 - a`**; it is not a ceiling for the published network (section D) -/
theorem scoped_ceiling (ε' lamp' κ' : ℝ) (hl : ((P.τ : ℚ) : ℝ) < lamp') (hε : 0 < ε')
    (h3 : κ' < ε' * (1 - lamp')) (h4 : κ' < (1 - ((P.τ : ℚ) : ℝ)) * (1 - ε')) :
    κ' < 37 / 25000000000 := by  -- json fast-gaussian.json scoped_ceiling.upper
  have hτ : ((P.τ : ℚ) : ℝ) = 1 - 296 / 10 ^ 11 := by norm_num [P]
  rw [hτ] at hl h4
  have := ceiling_half (1 - 296 / 10 ^ 11) ε' lamp' κ' (by norm_num) hl hε h3 h4
  linarith

/-- wording check on "g2, g3, g4 ≤ a·min{ε, 1-ε}" (note line 176, JSON
`scoped_ceiling.scope`): it holds for `min{g3, g4}` (`min_g3_g4_le`), but **not** for `g4`
alone at the witness, since `g4 = a(1-ε) > a·ε = a·min{ε, 1-ε}` -/
theorem g4_exceeds_a_min :
    P.g4 = (1 - P.τ) * (1 - P.ε) ∧ (1 - P.τ) * min P.ε (1 - P.ε) < P.g4 ∧
    P.g2 ≤ (1 - P.τ) * min P.ε (1 - P.ε) ∧ P.g3 ≤ (1 - P.τ) * min P.ε (1 - P.ε) := by
  norm_num [P, Params.g2, Params.g3, Params.g4, min_def]

/-- note lines 150-151: at `ε = 49999/100000`, `ζ = 1/10⁴`, the guard `εC1 < 1` with
`C1 = 5 - 4β + ζ` forces `β > 3/4` -/
theorem guard_forces_beta (β' : ℝ) (h : (49999 / 100000 : ℝ) * (5 - 4 * β' + 1 / 10000) < 1) :
    3 / 4 < β' := by
  linarith

/-- note line 151: the leaf condition `σ + β(1-σ) < λ'` is `(1-β)a_c > 1-λ'` -/
theorem leaf_iff (σ' β' lamp' : ℝ) :
    σ' + β' * (1 - σ') < lamp' ↔ 1 - lamp' < (1 - β') * (1 - σ') := by
  constructor <;> intro h <;> linarith

/-- note lines 152-153: with the original complex saving `418/10¹²` no `β` satisfies both
the guard and the leaf condition while keeping `g3 = ε(1-λ') > κ = 1479/10¹²` -/
theorem original_complex_infeasible (β' lamp' : ℝ)
    (hguard : (49999 / 100000 : ℝ) * (5 - 4 * β' + 1 / 10000) < 1)
    (hleaf : (1 - 418 / 10 ^ 12 : ℝ) + β' * (1 - (1 - 418 / 10 ^ 12)) < lamp')
    (hg3 : (1479 / 10 ^ 12 : ℝ) < 49999 / 100000 * (1 - lamp')) : False := by
  have hb := guard_forces_beta β' hguard
  linarith

/-- the chosen `β = 19/25` meets both with the compressed saving `14/10⁹` -/
theorem compressed_complex_feasible :
    (49999 / 100000 : ℚ) * (5 - 4 * (19 / 25) + 1 / 10000) < 1 ∧
    1 - P.lamp < (1 - 19 / 25) * (14 / 10 ^ 9) := by
  norm_num [P]

end Fast

/-! ## D. The ceiling for the published paired network -/

namespace Certified

/-- an admissible fast-Gaussian choice (audit witness): PR #5's `σ`, `β`, `C1`, and a `τ` the
same bit network certifies (`bit_exponent_29643`) -/
def Pw : Params :=
  { Fast.P with
    τ := 1 - 29643 / 10 ^ 13  -- audit
    lam := 1 - 296425 / 10 ^ 14  -- audit
    lamp := 1 - 29642 / 10 ^ 13  -- audit
    ε := 4999999 / 10 ^ 7  -- audit
    c := 1  -- audit
    δ := 1 / 10 ^ 8  -- audit
    κ := 14820 / 10 ^ 13 }  -- audit

theorem Pw_tau_certified : ((sb : ℕ) : ℝ) / (Wb : ℕ) < (125000 : ℝ) ^ ((Pw.τ : ℚ) : ℝ) := by
  have h : ((Pw.τ : ℚ) : ℝ) = 1 - 29643 / 10 ^ 13 := by norm_num [Pw, Fast.P]
  rw [h]; exact bit_exponent_29643

/-- negative control for `Fast.scoped_ceiling`: all 29 slacks and seven margins hold, with the
guard `C1 = 5 - 4β + ζ` and PR #5's certified `σ`, at `κ = 14820/10¹³ > a/2` -/
theorem fixed_tau_ceiling_beaten :
    Pw.FastOK ∧ Pw.FastAbsorbs ∧ Pw.C1 = 5 - 4 * Pw.β + ζ ∧ Pw.σ = Fast.P.σ ∧
    (37 / 25000000000 : ℚ) < Pw.κ := by
  unfold Params.FastOK Params.FastAbsorbs
  norm_num [Pw, Fast.P, ζ, Params.internal, Params.prep, Params.g1, Params.g2, Params.g3,
    Params.g4, Params.g5fast, Params.g6, Params.g7]

/-- **the ceiling for this network**: every `τ` it certifies, with `τ < λ' < 1`, `ε > 0` and
`κ` below `g3` and `g4`, gives `κ < 14825/10¹³ < 2^-29` -/
theorem certified_ceiling (τ' ε' lamp' κ' : ℝ)
    (hcert : ((sb : ℕ) : ℝ) / (Wb : ℕ) ≤ (125000 : ℝ) ^ τ') (hl : τ' < lamp') (hl1 : lamp' < 1)
    (hε : 0 < ε') (h3 : κ' < ε' * (1 - lamp')) (h4 : κ' < (1 - τ') * (1 - ε')) :
    κ' < 14825 / 10 ^ 13 ∧ κ' < 1 / 2 ^ 29 := by
  have hk := ceiling_half τ' ε' lamp' κ' (by linarith) hl hε h3 h4
  obtain ⟨-, -, -, hW, -, -, hs⟩ := bit_counts
  rw [hs, hW] at hcert
  have hsv := certified_saving_le 125000 ((50790175992864000000 : ℝ) / 406321422080000) τ'
    (by norm_num) (by norm_num) hcert
  have hpos : 0 < 1 - τ' := by linarith
  have : (1 - τ') * (117349 / 10000) < (1 - τ') * Real.log 125000 :=
    mul_lt_mul_of_pos_left log_125000_gt hpos
  norm_num at hsv this ⊢
  constructor <;> linarith

/-- non-vacuity and tightness: the witness meets every hypothesis of `certified_ceiling`, so no
ceiling below `14820/10¹³` holds; the stated one is `5/10¹³` above it -/
theorem certified_ceiling_attained :
    ((Pw.κ : ℚ) : ℝ) < 14825 / 10 ^ 13 ∧ (14825 / 10 ^ 13 : ℚ) - Pw.κ = 5 / 10 ^ 13 := by
  refine ⟨(certified_ceiling (Pw.τ : ℝ) (Pw.ε : ℝ) (Pw.lamp : ℝ) (Pw.κ : ℝ)
    Pw_tau_certified.le ?_ ?_ ?_ ?_ ?_).1, by norm_num [Pw, Fast.P]⟩ <;>
    norm_num [Pw, Fast.P]

end Certified

end PRChecksB.PR5
