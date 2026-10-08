import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The copied-centre lemma

Two versions are formalized:

* `notes/copied-centers-lemma.tex` (retained centres, used by the selected witness): a
  retained centre at `D_U` with `dim U = r` changes its rank profile from `z^r + z^h` to
  `z^r + z^(h-r)`, in both invocation orientations;
* `research/swapnil-parallel/upstream/notes/copied-centres.tex` (direct centres): the frame
  path `D₀ → D₁ → D₀ → D₁` (ranks `h, h, h`) becomes `D₀ → D₁` for the original plus
  `D₁ → D₀` for the copy (ranks `h, h`).

**Model.** A role's physical stream holds `F_Q w`, where `w` is its scalar value and
`F_Q` is the (invertible, linear) address frame of `Q`. Changing frame applies
`F_{Q₂} F_{Q₁}⁻¹`. A pointwise scalar gate acts on streams that share one frame; by
linearity it then acts on the scalar values. A fresh zero stream is `0` in every frame.

Section 1 proves that the copied schedules produce exactly the same streams as the
original ones for all inputs, including arbitrary dirty centre values, and that the
centre is restored. Section 2 proves the rank charges from the subspace construction
`D_U = D₀ ⊔ (P ⊗ U)`, `D₁ = D₀ ⊔ (P ⊗ F)`. Section 3 proves the histogram and rank-mass
bookkeeping `s = Wm - N + L` and checks the selected networks' numbers.

Not modelled: that the copy's frame change compiles to the stated batched profile
(it is the old edge's matrix), and the tape schedule.
-/

namespace KappaCheck.CopiedCentres

open Module

/-! ## 1. Scalar action -/

section Scalar

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] (F : ι → M ≃ₗ[R] M)

/-- change a physical stream from frame `q₁` to frame `q₂` -/
def move (q₁ q₂ : ι) (s : M) : M := F q₂ ((F q₁).symm s)

@[simp] theorem move_frame (q₁ q₂ : ι) (w : M) : move F q₁ q₂ (F q₁ w) = F q₂ w := by
  simp [move]

theorem move_move (q₁ q₂ q₃ : ι) (s : M) :
    move F q₂ q₃ (move F q₁ q₂ s) = move F q₁ q₃ s := by
  simp [move]

/-- a pointwise gate commutes with a frame: `F (u + a • v) = F u + a • F v` -/
theorem gate_frame (q : ι) (a : R) (u v : M) : F q (u + a • v) = F q u + a • F q v := by
  simp

/-- **Direct centres, old word** (`copied-centres.tex` lines 14-17). Streams: `px` at the
gather frame `D₁`, `py` at the scatter frame `D₀`, the centre `pc` starting at `D₀`.
Scatter old value, rise, gather, return (rank `h`), scatter new value, re-rise (rank `h`),
cleanup gather. -/
def directOld (D₀ D₁ : ι) (k l : R) (px py pc : M) : M × M × M :=
  let py₁ := py - l • pc
  let pc₁ := move F D₀ D₁ pc
  let pc₂ := pc₁ + k • px
  let pc₃ := move F D₁ D₀ pc₂
  let py₂ := py₁ + l • pc₃
  let pc₄ := move F D₀ D₁ pc₃
  let pc₅ := pc₄ - k • px
  (px, py₂, pc₅)

/-- **Direct centres, copied word** (`copied-centres.tex` lines 19-25): after the first
gather copy `c` into a fresh zero stream at `D₁`, move only the copy to `D₀`, read it,
erase it; the original stays at `D₁`. -/
def directCopied (D₀ D₁ : ι) (k l : R) (px py pc : M) : M × M × M :=
  let py₁ := py - l • pc
  let pc₁ := move F D₀ D₁ pc
  let pc₂ := pc₁ + k • px
  let pt₁ := (0 : M) + pc₂
  let pt₂ := move F D₁ D₀ pt₁
  let py₂ := py₁ + l • pt₂
  let pc₅ := pc₂ - k • px
  (px, py₂, pc₅)

/-- the copied word produces exactly the same streams, for every input -/
theorem direct_same (D₀ D₁ : ι) (k l : R) (px py pc : M) :
    directCopied F D₀ D₁ k l px py pc = directOld F D₀ D₁ k l px py pc := by
  simp [directCopied, directOld, move]

/-- its scalar action: `y ← y + l k x`, and an arbitrary centre value `c` is restored
(ending at `D₁`) -/
theorem direct_action (D₀ D₁ : ι) (k l : R) (x y c : M) :
    directCopied F D₀ D₁ k l (F D₁ x) (F D₀ y) (F D₀ c) =
      (F D₁ x, F D₀ (y + (l * k) • x), F D₁ c) := by
  simp only [directCopied, move_frame, zero_add, Prod.mk.injEq, true_and]
  constructor
  · simp only [move, LinearEquiv.symm_apply_apply, map_add, map_smul, mul_smul, map_sub,
      smul_add]
    abel
  · simp

variable {n : ℕ}

/-- **Retained centres, forward orientation** (`copied-centers-lemma.tex` lines 45-48):
the centre at `D_U` moves to `D₀` (rank `r`), feeds `n` scatter reads, then moves to `D₁`
(rank `h`) for its cleanup `cont`. -/
def forwardOld (DU D₀ D₁ : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    (Fin n → M) × M :=
  let pc₁ := move F DU D₀ pc
  let ys' := fun j => ys j + l j • pc₁
  (ys', cont (move F D₀ D₁ pc₁))

/-- forward copied schedule (lines 49-56): copy at `D_U`, move only the copy to `D₀`
(rank `r`), read it, erase it, move the original directly `D_U → D₁` (rank `h - r`) -/
def forwardCopied (DU D₀ D₁ : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    (Fin n → M) × M :=
  let pt := move F DU D₀ ((0 : M) + pc)
  let ys' := fun j => ys j + l j • pt
  (ys', cont (move F DU D₁ pc))

theorem forward_same (DU D₀ D₁ : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    forwardCopied F DU D₀ D₁ l cont ys pc = forwardOld F DU D₀ D₁ l cont ys pc := by
  simp [forwardCopied, forwardOld, move_move]

/-- **Retained centres, reverse orientation** (lines 58-66): the centre at `D₀` moves to
`D₁` (rank `h`), feeds the scatter reads, then moves to `D_{U⊥}` (rank `r`). -/
def reverseOld (D₀ D₁ DUp : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    (Fin n → M) × M :=
  let pc₁ := move F D₀ D₁ pc
  let ys' := fun j => ys j + l j • pc₁
  (ys', cont (move F D₁ DUp pc₁))

/-- reverse copied schedule: advance the original directly `D₀ → D_{U⊥}` (rank `h - r`),
copy it there, move the copy to `D₁` (rank `r`), read it, erase it -/
def reverseCopied (D₀ D₁ DUp : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    (Fin n → M) × M :=
  let pc₁ := move F D₀ DUp pc
  let pt := move F DUp D₁ ((0 : M) + pc₁)
  let ys' := fun j => ys j + l j • pt
  (ys', cont pc₁)

theorem reverse_same (D₀ D₁ DUp : ι) (l : Fin n → R) (cont : M → M) (ys : Fin n → M) (pc : M) :
    reverseCopied F D₀ D₁ DUp l cont ys pc = reverseOld F D₀ D₁ DUp l cont ys pc := by
  simp [reverseCopied, reverseOld, move_move]

end Scalar

/-! ## 2. Rank charges from the frame construction -/

section Rank

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- the rank charged for changing between two frames: `|dim Q₂ - dim Q₁|` -/
noncomputable def charge (Q₁ Q₂ : Submodule K V) : ℕ :=
  Int.natAbs ((finrank K Q₂ : ℤ) - finrank K Q₁)

/-- `dim (D ⊔ E) = dim D + dim E` when `D ⊓ E = ⊥` -/
theorem finrank_sup_of_disjoint (D E : Submodule K V) (h : D ⊓ E = ⊥) :
    finrank K ↥(D ⊔ E) = finrank K D + finrank K E := by
  have := Submodule.finrank_sup_add_finrank_inf_eq D E
  rw [h, finrank_bot, add_zero] at this
  exact this

/-- the frames of one invocation: `D_U = D₀ ⊔ E_U`, `D_{U⊥} = D₀ ⊔ E_{U⊥}`,
`D₁ = D₀ ⊔ E_F`, where `E_U = P ⊗ U` (dim `r`), `E_{U⊥} = P ⊗ U⊥` (dim `h - r`) and
`E_F = P ⊗ F` (dim `h`) are orthogonal to `D₀` (lines 15-22) -/
structure Frames (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  D₀ : Submodule K V
  EU : Submodule K V
  EUp : Submodule K V
  EF : Submodule K V
  hU : EU ≤ EF
  hUp : EUp ≤ EF
  disj : D₀ ⊓ EF = ⊥

variable (f : Frames K V)

def Frames.DU := f.D₀ ⊔ f.EU
def Frames.DUp := f.D₀ ⊔ f.EUp
def Frames.D₁ := f.D₀ ⊔ f.EF

theorem Frames.dim_DU : finrank K f.DU = finrank K f.D₀ + finrank K f.EU :=
  finrank_sup_of_disjoint _ _ (le_bot_iff.1 (f.disj ▸ inf_le_inf_left _ f.hU))

theorem Frames.dim_DUp : finrank K f.DUp = finrank K f.D₀ + finrank K f.EUp :=
  finrank_sup_of_disjoint _ _ (le_bot_iff.1 (f.disj ▸ inf_le_inf_left _ f.hUp))

theorem Frames.dim_D₁ : finrank K f.D₁ = finrank K f.D₀ + finrank K f.EF :=
  finrank_sup_of_disjoint _ _ f.disj

omit [FiniteDimensional K V] in
/-- the frames are nested: `D₀ ≤ D_U ≤ D₁` and `D₀ ≤ D_{U⊥} ≤ D₁` -/
theorem Frames.nested : f.D₀ ≤ f.DU ∧ f.DU ≤ f.D₁ ∧ f.D₀ ≤ f.DUp ∧ f.DUp ≤ f.D₁ :=
  ⟨le_sup_left, sup_le_sup_left f.hU _, le_sup_left, sup_le_sup_left f.hUp _⟩

/-- **Forward orientation**: old path `D_U → D₀ → D₁` charges `r + h`; copied schedule
charges `r` (copy `D_U → D₀`) plus `h - r` (original `D_U → D₁`). -/
theorem forward_charges (r h : ℕ) (hr : finrank K f.EU = r) (hh : finrank K f.EF = h) :
    charge f.DU f.D₀ + charge f.D₀ f.D₁ = r + h ∧
    charge f.DU f.D₀ + charge f.DU f.D₁ = r + (h - r) := by
  have hrh : r ≤ h := hr ▸ hh ▸ Submodule.finrank_mono f.hU
  simp only [charge, f.dim_DU, f.dim_D₁, hr, hh]
  constructor <;> omega

/-- **Reverse orientation**: old path `D₀ → D₁ → D_{U⊥}` charges `h + r`; copied schedule
charges `h - r` (original `D₀ → D_{U⊥}`) plus `r` (copy `D_{U⊥} → D₁`), when
`dim U⊥ = h - r`. -/
theorem reverse_charges (r h : ℕ) (hr : finrank K f.EUp = h - r) (hh : finrank K f.EF = h)
    (hrh : r ≤ h) :
    charge f.D₀ f.D₁ + charge f.D₁ f.DUp = h + r ∧
    charge f.D₀ f.DUp + charge f.DUp f.D₁ = (h - r) + r := by
  simp only [charge, f.dim_DUp, f.dim_D₁, hr, hh]
  constructor <;> omega

/-- **Direct centres**: old path `D₀ → D₁ → D₀ → D₁` charges `3h`; copied schedule charges
`h` (original `D₀ → D₁`) plus `h` (copy `D₁ → D₀`). -/
theorem direct_charges (h : ℕ) (hh : finrank K f.EF = h) :
    charge f.D₀ f.D₁ + charge f.D₁ f.D₀ + charge f.D₀ f.D₁ = 3 * h ∧
    charge f.D₀ f.D₁ + charge f.D₁ f.D₀ = 2 * h := by
  simp only [charge, f.dim_D₁, hh]
  constructor <;> omega

end Rank

/-! ## 3. Histogram and rank mass -/

section Mass

open Finset

/-- **Lines 79-86**: with `r = h - 1`, each of the `h` retained centres of an invocation
turns one rank-`h` child into a rank-one child, so the rank mass drops by `ℓ_h = h(h-1)`. -/
theorem histogram_update (H : ℕ → ℤ) (h n : ℕ) (h1 : 1 < h) (hn : h < n) :
    ∑ r ∈ range n, (r : ℤ) * (H r + (if r = 1 then (h : ℤ) else 0) - (if r = h then (h : ℤ) else 0)) =
      ∑ r ∈ range n, (r : ℤ) * H r - h * (h - 1) := by
  have e : ∀ r : ℕ, (r : ℤ) * (H r + (if r = 1 then (h : ℤ) else 0) - (if r = h then (h : ℤ) else 0)) =
      r * H r + (if r = 1 then (r : ℤ) * h else 0) - (if r = h then (r : ℤ) * h else 0) := by
    intro r; rw [mul_sub, mul_add, mul_ite, mul_ite, mul_zero]
  simp only [e, sum_sub_distrib, sum_add_distrib, sum_ite_eq', mem_range]
  rw [if_pos (by omega), if_pos hn]
  push_cast
  ring

/-- **Lines 92-100**: two factors `a, b`; subtracting `L = v_b ℓ_a + v_a ℓ_b` from the old
mass `Wm - N + 2L` gives `s = Wm - N + L`, so `Wm - s = N - L`. -/
theorem rank_mass (va vb Ra Rb la lb m : ℤ) :
    let N := va * vb
    let W := 2 * N + vb * Ra + va * Rb
    let L := vb * la + va * lb
    let s := (W * m - N + 2 * L) - L
    s = W * m - N + L ∧ W * m - s = N - L := by
  intro N W L s
  constructor <;> simp only [s] <;> ring

/-- the selected `(23, 25)` network (`docs/research/community-round2-review.md`):
`N = 4073300`, `L = 2226400`, `Wm - s = 1846900`, `s = 78860441550` at `W = 137151806` -/
theorem selected_network :
    let va : ℤ := (Nat.choose 23 3 : ℕ)
    let vb : ℤ := (Nat.choose 25 3 : ℕ)
    let N := va * vb
    let L := vb * (23 * 22) + va * (25 * 24)
    N = 4073300 ∧ L = 2226400 ∧ N - L = 1846900 ∧
      (137151806 : ℤ) * 575 - N + L = 78860441550 := by
  intro va vb N L
  simp only [N, L, va, vb]
  norm_num [Nat.choose]

/-- Swapnil's direct centres (round six, `h = 25`): `L = 2 v h c₀` with `c₀ = h`, and the
deficit `N - L = v(v - 2h²) = 2415000` -/
theorem direct_deficit :
    let v : ℤ := (Nat.choose 25 3 : ℕ)
    v * v - 2 * v * 25 * 25 = v * (v - 2 * 25 ^ 2) ∧ v * v - 2 * v * 25 * 25 = 2415000 := by
  intro v
  simp only [v]
  norm_num [Nat.choose]

/-- Swapnil's retained point totals (round six, `h = 23`): loss `h - 1` per centre, so
`L = 2 v h (h - 1)` and `N - L = 1344189`, the deficit of `lean/Round6.lean`'s bit
histogram (`148225616 · 529 - 78410006675`) -/
theorem retained_totals_deficit :
    let v : ℤ := (Nat.choose 23 3 : ℕ)
    v * v - 2 * v * 23 * 22 = 1344189 ∧ (148225616 : ℤ) * 529 - 78410006675 = 1344189 := by
  intro v
  simp only [v]
  norm_num [Nat.choose]

end Mass

end KappaCheck.CopiedCentres
