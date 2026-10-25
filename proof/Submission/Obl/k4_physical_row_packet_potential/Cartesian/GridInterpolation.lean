-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/GridInterpolation.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/GridInterpolation.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0358 (as merged
-- on branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/GridInterpolation.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.SeparatedGridTargets
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.TensorFieldError

/-!
# A polynomial field on an original-law grid from common fiber tables

Paper `tex-06-isotropic.tex`, Section 6, "Cartesian interpolation of the physical field", in
the finite original-law form requested by x0352 (o106).  Incidences carry a grid code
`code : Ω → S × S × S` on a finite `ξ`-separated real grid `S` (values bounded by `A`); a
scalar field `V` on grid cells is bounded by `B` on heavy cells (original cell mass `≥ a`),
and along each axis it is `ε`-close on heavy cells to common fiber polynomials of degree
`≤ D` (`Px y z`, `Py x z`, `Pz x y`).  Then one actual polynomial `P` of total degree
`≤ 3 D` with controlled coefficients satisfies
`|V (code ω) - P (code ω)| ≤ 3 (1 + (D + 1) (2 A / r)^D)^3 ε` on an original target family of
explicit mass.

The anchors and targets come from x0352's `original_separated_grid_targets`
(`SeparatedGridTargets.lean`); the interpolant and its error from `TensorField.lean` and
`TensorFieldError.lean`.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set MvPolynomial Cartesian

noncomputable section

/-- The real coordinates of a grid cell. -/
def gridPoint {S : Finset ℝ} (g : S × S × S) : Fin 3 → ℝ :=
  ![(g.1 : ℝ), (g.2.1 : ℝ), (g.2.2 : ℝ)]

/-- Choose the anchor `i` or, for `none`, the target coordinate. -/
def anchorOrTarget {X : Type*} {k : ℕ} (xs : Fin k → X) (t : X) : Option (Fin k) → X
  | none => t
  | some i => xs i

theorem anchorOrTarget_eq_snoc {X : Type*} {k : ℕ} (xs : Fin k → X) (t : X) (o : Option (Fin k)) :
    anchorOrTarget xs t o = (Fin.snoc xs t : Fin (k + 1) → X)
      (match o with | none => Fin.last k | some i => Fin.castSucc i) := by
  cases o with
  | none => simp [anchorOrTarget]
  | some i => simp [anchorOrTarget]

/-- **Error at one target** (no measure): if all mixed vertices of the anchors `xs, ys, zs` and
the target `g` are `heavy`, and on heavy cells `V` is `ε`-close to the common fiber tables,
the tensor interpolant of the anchor values is `3 (1 + (D + 1) (2 A / r)^D)^3 ε`-close to
`V g`. -/
theorem grid_tensor_error {S : Finset ℝ} (D : ℕ) (xs ys zs : Fin (D + 1) → S)
    (r A ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε) (hA : ∀ s ∈ S, |s| ≤ A)
    (hanch : anchorsSeparated (fun x : S => (x : ℝ)) r (xs, ys, zs))
    (heavy : S × S × S → Prop) (g : S × S × S)
    (hheavy : ∀ i j l : Fin (D + 1 + 1), heavy ((Fin.snoc xs g.1 : Fin (D + 1 + 1) → S) i,
      (Fin.snoc ys g.2.1 : Fin (D + 1 + 1) → S) j, (Fin.snoc zs g.2.2 : Fin (D + 1 + 1) → S) l))
    (V : S × S × S → ℝ) (Px Py Pz : S → S → Polynomial ℝ)
    (hPx : ∀ y z, (Px y z).natDegree ≤ D) (hPy : ∀ x z, (Py x z).natDegree ≤ D)
    (hPz : ∀ x y, (Pz x y).natDegree ≤ D)
    (hfx : ∀ g, heavy g → |V g - (Px g.2.1 g.2.2).eval (g.1 : ℝ)| ≤ ε)
    (hfy : ∀ g, heavy g → |V g - (Py g.1 g.2.2).eval (g.2.1 : ℝ)| ≤ ε)
    (hfz : ∀ g, heavy g → |V g - (Pz g.1 g.2.1).eval (g.2.2 : ℝ)| ≤ ε) :
    |V g - eval (gridPoint g) (tensorPoly (fun i => (xs i : ℝ)) (fun i => (ys i : ℝ))
        (fun i => (zs i : ℝ)) (fun i j l => V (xs i, ys j, zs l)))| ≤
      3 * (1 + ((D : ℝ) + 1) * ((2 * A) / r) ^ D) ^ 3 * ε := by
  set ax : Fin (D + 1) → ℝ := fun i => (xs i : ℝ) with hax
  set ay : Fin (D + 1) → ℝ := fun i => (ys i : ℝ) with hay
  set az : Fin (D + 1) → ℝ := fun i => (zs i : ℝ) with haz
  have hsepx : ∀ i j, i ≠ j → r ≤ |ax i - ax j| := fun i j hij => hanch 0 i j hij
  have hsepy : ∀ i j, i ≠ j → r ≤ |ay i - ay j| := fun i j hij => hanch 1 i j hij
  have hsepz : ∀ i j, i ≠ j → r ≤ |az i - az j| := fun i j hij => hanch 2 i j hij
  have hinj : ∀ (n : Fin (D + 1) → ℝ), (∀ i j, i ≠ j → r ≤ |n i - n j|) →
      Function.Injective n := by
    intro n hn i j hij
    by_contra hne
    have := hn i j hne
    rw [hij, sub_self, abs_zero] at this
    linarith
  have hAx : ∀ i, |ax i| ≤ A := fun i => hA _ (xs i).2
  have hAy : ∀ i, |ay i| ≤ A := fun i => hA _ (ys i).2
  have hAz : ∀ i, |az i| ≤ A := fun i => hA _ (zs i).2
  have hheavy' : ∀ o₁ o₂ o₃, heavy
      (anchorOrTarget xs g.1 o₁, anchorOrTarget ys g.2.1 o₂, anchorOrTarget zs g.2.2 o₃) := by
    intro o₁ o₂ o₃
    rw [anchorOrTarget_eq_snoc, anchorOrTarget_eq_snoc, anchorOrTarget_eq_snoc]
    exact hheavy _ _ _
  set f : Option (Fin (D + 1)) → Option (Fin (D + 1)) → Option (Fin (D + 1)) → ℝ :=
    fun o₁ o₂ o₃ => V (anchorOrTarget xs g.1 o₁, anchorOrTarget ys g.2.1 o₂,
      anchorOrTarget zs g.2.2 o₃) with hf
  have hR : ∀ v, |gridPoint g v| ≤ A := by
    intro v
    fin_cases v
    · exact hA _ g.1.2
    · exact hA _ g.2.1.2
    · exact hA _ g.2.2.2
  have hv000 : heavy g := by
    have h := hheavy' none none none
    simp only [anchorOrTarget, Prod.mk.eta] at h
    exact h
  have hvi00 : ∀ i, heavy (xs i, g.2.1, g.2.2) := fun i => by
    have h := hheavy' (some i) none none
    simp only [anchorOrTarget] at h
    exact h
  have hvij0 : ∀ i j, heavy (xs i, ys j, g.2.2) := fun i j => by
    have h := hheavy' (some i) (some j) none
    simp only [anchorOrTarget] at h
    exact h
  have hvijl : ∀ i j l, heavy (xs i, ys j, zs l) := fun i j l => by
    have h := hheavy' (some i) (some j) (some l)
    simp only [anchorOrTarget] at h
    exact h
  have hx : ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      |f none none none - p.eval (gridPoint g 0)| ≤ ε ∧
      ∀ i, |f (some i) none none - p.eval (ax i)| ≤ ε := by
    refine ⟨Px g.2.1 g.2.2, hPx _ _, ?_, fun i => ?_⟩
    · have h := hfx g hv000
      simpa [hf, anchorOrTarget, gridPoint] using h
    · have h := hfx (xs i, g.2.1, g.2.2) (hvi00 i)
      simpa [hf, anchorOrTarget] using h
  have hy : ∀ i, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      |f (some i) none none - p.eval (gridPoint g 1)| ≤ ε ∧
      ∀ j, |f (some i) (some j) none - p.eval (ay j)| ≤ ε := by
    intro i
    refine ⟨Py (xs i) g.2.2, hPy _ _, ?_, fun j => ?_⟩
    · have h := hfy (xs i, g.2.1, g.2.2) (hvi00 i)
      simpa [hf, anchorOrTarget, gridPoint] using h
    · have h := hfy (xs i, ys j, g.2.2) (hvij0 i j)
      simpa [hf, anchorOrTarget] using h
  have hz : ∀ i j, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      |f (some i) (some j) none - p.eval (gridPoint g 2)| ≤ ε ∧
      ∀ l, |f (some i) (some j) (some l) - p.eval (az l)| ≤ ε := by
    intro i j
    refine ⟨Pz (xs i) (ys j), hPz _ _, ?_, fun l => ?_⟩
    · have h := hfz (xs i, ys j, g.2.2) (hvij0 i j)
      simpa [hf, anchorOrTarget, gridPoint] using h
    · have h := hfz (xs i, ys j, zs l) (hvijl i j l)
      simpa [hf, anchorOrTarget] using h
  have key := abs_sub_eval_tensorPoly_le ax ay az (hinj ax hsepx) (hinj ay hsepy)
    (hinj az hsepz) A r A ε hr hε hAx hAy hAz hsepx hsepy hsepz (gridPoint g) hR f hx hy hz
  have hf0 : f none none none = V g := by simp [hf, anchorOrTarget]
  have hfP : (fun i j l => f (some i) (some j) (some l)) =
      (fun i j l => V (xs i, ys j, zs l)) := by
    funext i j l; simp [hf, anchorOrTarget]
  rw [hf0, hfP] at key
  have h2A : A + A = 2 * A := by ring
  rw [h2A] at key
  exact key

/-- **Polynomial field on an original grid.**  For each degree `D` one coefficient constant `C`
works for all grids, measures and fields. -/
theorem original_grid_polynomial_field (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
      (S : Finset ℝ) [Nonempty S] (code : Ω → S × S × S), Measurable code →
      ∀ (a U δ ξ r A B ε : ℝ), 0 < a → 0 < U → 0 ≤ δ → 0 < ξ → 0 < r → 0 ≤ B → 0 ≤ ε →
      (∀ s ∈ S, |s| ≤ A) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ξ ≤ dist x y) →
      (∀ i : S × S × S, μ.real {x | code x = i} ≤ U) →
      δ * U * (S.card : ℝ) ^ 3 + (S.card : ℝ) ^ 3 * a ≤ μ.real univ →
      3 * ((D + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ)) < δ ^ ((D + 2) ^ 3) →
      ∀ (V : S × S × S → ℝ), (∀ g, a ≤ μ.real {x | code x = g} → |V g| ≤ B) →
      ∀ (Px Py Pz : S → S → Polynomial ℝ),
      (∀ y z, (Px y z).natDegree ≤ D) → (∀ x z, (Py x z).natDegree ≤ D) →
      (∀ x y, (Pz x y).natDegree ≤ D) →
      (∀ g, a ≤ μ.real {x | code x = g} → |V g - (Px g.2.1 g.2.2).eval (g.1 : ℝ)| ≤ ε) →
      (∀ g, a ≤ μ.real {x | code x = g} → |V g - (Py g.1 g.2.2).eval (g.2.1 : ℝ)| ≤ ε) →
      (∀ g, a ≤ μ.real {x | code x = g} → |V g - (Pz g.1 g.2.1).eval (g.2.2 : ℝ)| ≤ ε) →
      ∃ (P : MvPolynomial (Fin 3) ℝ) (G : Finset (S × S × S)),
        P.totalDegree ≤ 3 * D ∧
        (∀ d, |P.coeff d| ≤ C * (((D : ℝ) + 1) ^ 3 * B * ((1 + A) / r) ^ (3 * D))) ∧
        MeasurableSet {x | code x ∈ G} ∧
        (δ ^ ((D + 2) ^ 3) - 3 * ((D + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ))) / 2 *
          a * (S.card : ℝ) ^ 3 ≤ μ.real {x | code x ∈ G} ∧
        ∀ ω, code ω ∈ G →
          |V (code ω) - eval (gridPoint (code ω)) P| ≤
            3 * (1 + ((D : ℝ) + 1) * ((2 * A) / r) ^ D) ^ 3 * ε := by
  obtain ⟨C, hC, hcoef⟩ := exists_tensorPoly_coeff_bound D
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ S _ code hcode a U δ ξ r A B ε ha hU hδ hξ hr hB hε hA hsep hcap hbudget hgap
    V hVB Px Py Pz hPx hPy hPz hfx hfy hfz
  have hgap' : 3 * ((D + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ)) <
      δ ^ ((D + 1 + 1) ^ 3) := by simpa using hgap
  obtain ⟨xs, ys, zs, G, hanch, hheavy, hmass⟩ :=
    original_separated_grid_targets μ S code hcode a U δ ξ r ha hU hδ hξ hr hsep hcap hbudget
      (D + 1) hgap'
  -- real anchors
  set ax : Fin (D + 1) → ℝ := fun i => (xs i : ℝ) with hax
  set ay : Fin (D + 1) → ℝ := fun i => (ys i : ℝ) with hay
  set az : Fin (D + 1) → ℝ := fun i => (zs i : ℝ) with haz
  have hsepx : ∀ i j, i ≠ j → r ≤ |ax i - ax j| := fun i j hij => hanch 0 i j hij
  have hsepy : ∀ i j, i ≠ j → r ≤ |ay i - ay j| := fun i j hij => hanch 1 i j hij
  have hsepz : ∀ i j, i ≠ j → r ≤ |az i - az j| := fun i j hij => hanch 2 i j hij
  have hinj : ∀ (n : Fin (D + 1) → ℝ), (∀ i j, i ≠ j → r ≤ |n i - n j|) → Function.Injective n := by
    intro n hn i j hij
    by_contra hne
    have := hn i j hne
    rw [hij, sub_self, abs_zero] at this
    linarith
  have hAx : ∀ i, |ax i| ≤ A := fun i => hA _ (xs i).2
  have hAy : ∀ i, |ay i| ≤ A := fun i => hA _ (ys i).2
  have hAz : ∀ i, |az i| ≤ A := fun i => hA _ (zs i).2
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hAx 0)
  -- the target family is nonempty, so all pure anchor vertices are heavy
  have hβ : 0 < (δ ^ ((D + 2) ^ 3) - 3 * ((D + 1 : ℕ) : ℝ) ^ 2 *
      ((2 * r / ξ + 1) / (S.card : ℝ))) / 2 * a * (S.card : ℝ) ^ 3 := by
    have hcard : (0 : ℝ) < S.card := by
      have : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_coe_sort.mp inferInstance)
      exact_mod_cast this
    have := sub_pos.mpr hgap
    positivity
  have hGne : G.Nonempty := by
    by_contra hG
    rw [Finset.not_nonempty_iff_eq_empty] at hG
    subst hG
    simp only [Finset.notMem_empty, Set.ofPred_false, measureReal_empty] at hmass
    linarith
  obtain ⟨g₀, hg₀⟩ := hGne
  have hVanchor : ∀ i j l, |V (xs i, ys j, zs l)| ≤ B := by
    intro i j l
    apply hVB
    have := hheavy g₀ hg₀ (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc l)
    simpa only [Fin.snoc_castSucc] using this
  -- the interpolant
  set P := tensorPoly ax ay az (fun i j l => V (xs i, ys j, zs l)) with hP
  refine ⟨P, G, totalDegree_tensorPoly_le ax ay az _, ?_, ?_, hmass, ?_⟩
  · exact hcoef ax ay az A r B hr hA0 hB hAx hAy hAz hsepx hsepy hsepz _
      (fun i j l => hVanchor i j l)
  · exact hcode (Set.Finite.measurableSet (G.finite_toSet))
  · intro ω hω
    set g := code ω with hg
    -- the field on mixed vertices: anchors or the target's own coordinates
    set f : Option (Fin (D + 1)) → Option (Fin (D + 1)) → Option (Fin (D + 1)) → ℝ :=
      fun o₁ o₂ o₃ => V (anchorOrTarget xs g.1 o₁, anchorOrTarget ys g.2.1 o₂,
        anchorOrTarget zs g.2.2 o₃) with hf
    have hheavy' : ∀ o₁ o₂ o₃, a ≤ μ.real {x | code x =
        (anchorOrTarget xs g.1 o₁, anchorOrTarget ys g.2.1 o₂, anchorOrTarget zs g.2.2 o₃)} := by
      intro o₁ o₂ o₃
      rw [anchorOrTarget_eq_snoc, anchorOrTarget_eq_snoc, anchorOrTarget_eq_snoc]
      exact hheavy g hω _ _ _
    have hR : ∀ v, |gridPoint g v| ≤ A := by
      intro v
      fin_cases v
      · exact hA _ g.1.2
      · exact hA _ g.2.1.2
      · exact hA _ g.2.2.2
    -- the six fiber facts at heavy mixed vertices
    have hv000 : a ≤ μ.real {x | code x = g} := by
      have h := hheavy' none none none
      simp only [anchorOrTarget, Prod.mk.eta] at h
      exact h
    have hvi00 : ∀ i, a ≤ μ.real {x | code x = (xs i, g.2.1, g.2.2)} := fun i => by
      have h := hheavy' (some i) none none
      simp only [anchorOrTarget] at h
      exact h
    have hvij0 : ∀ i j, a ≤ μ.real {x | code x = (xs i, ys j, g.2.2)} := fun i j => by
      have h := hheavy' (some i) (some j) none
      simp only [anchorOrTarget] at h
      exact h
    have hvijl : ∀ i j l, a ≤ μ.real {x | code x = (xs i, ys j, zs l)} := fun i j l => by
      have h := hheavy' (some i) (some j) (some l)
      simp only [anchorOrTarget] at h
      exact h
    have hx : ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
        |f none none none - p.eval (gridPoint g 0)| ≤ ε ∧
        ∀ i, |f (some i) none none - p.eval (ax i)| ≤ ε := by
      refine ⟨Px g.2.1 g.2.2, hPx _ _, ?_, fun i => ?_⟩
      · have h := hfx g hv000
        simpa [hf, anchorOrTarget, gridPoint] using h
      · have h := hfx (xs i, g.2.1, g.2.2) (hvi00 i)
        simpa [hf, anchorOrTarget] using h
    have hy : ∀ i, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
        |f (some i) none none - p.eval (gridPoint g 1)| ≤ ε ∧
        ∀ j, |f (some i) (some j) none - p.eval (ay j)| ≤ ε := by
      intro i
      refine ⟨Py (xs i) g.2.2, hPy _ _, ?_, fun j => ?_⟩
      · have h := hfy (xs i, g.2.1, g.2.2) (hvi00 i)
        simpa [hf, anchorOrTarget, gridPoint] using h
      · have h := hfy (xs i, ys j, g.2.2) (hvij0 i j)
        simpa [hf, anchorOrTarget] using h
    have hz : ∀ i j, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
        |f (some i) (some j) none - p.eval (gridPoint g 2)| ≤ ε ∧
        ∀ l, |f (some i) (some j) (some l) - p.eval (az l)| ≤ ε := by
      intro i j
      refine ⟨Pz (xs i) (ys j), hPz _ _, ?_, fun l => ?_⟩
      · have h := hfz (xs i, ys j, g.2.2) (hvij0 i j)
        simpa [hf, anchorOrTarget, gridPoint] using h
      · have h := hfz (xs i, ys j, zs l) (hvijl i j l)
        simpa [hf, anchorOrTarget] using h
    have key := abs_sub_eval_tensorPoly_le ax ay az (hinj ax hsepx) (hinj ay hsepy)
      (hinj az hsepz) A r A ε hr hε hAx hAy hAz hsepx hsepy hsepz (gridPoint g) hR f hx hy hz
    have hf0 : f none none none = V g := by simp [hf, anchorOrTarget]
    have hfP : (fun i j l => f (some i) (some j) (some l)) = (fun i j l => V (xs i, ys j, zs l)) :=
      by funext i j l; simp [hf, anchorOrTarget]
    rw [hf0, hfP] at key
    have h2A : A + A = 2 * A := by ring
    rw [h2A] at key
    exact key

/-- **Row version** with ONE target family `G` for all `q` coordinates of a row-valued field. -/
theorem original_grid_polynomial_field_row (D q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
      (S : Finset ℝ) [Nonempty S] (code : Ω → S × S × S), Measurable code →
      ∀ (a U δ ξ r A B ε : ℝ), 0 < a → 0 < U → 0 ≤ δ → 0 < ξ → 0 < r → 0 ≤ B → 0 ≤ ε →
      (∀ s ∈ S, |s| ≤ A) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ξ ≤ dist x y) →
      (∀ i : S × S × S, μ.real {x | code x = i} ≤ U) →
      δ * U * (S.card : ℝ) ^ 3 + (S.card : ℝ) ^ 3 * a ≤ μ.real univ →
      3 * ((D + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ)) < δ ^ ((D + 2) ^ 3) →
      ∀ (V : S × S × S → Fin q → ℝ), (∀ g e, a ≤ μ.real {x | code x = g} → |V g e| ≤ B) →
      ∀ (Px Py Pz : Fin q → S → S → Polynomial ℝ),
      (∀ e y z, (Px e y z).natDegree ≤ D) → (∀ e x z, (Py e x z).natDegree ≤ D) →
      (∀ e x y, (Pz e x y).natDegree ≤ D) →
      (∀ g e, a ≤ μ.real {x | code x = g} → |V g e - (Px e g.2.1 g.2.2).eval (g.1 : ℝ)| ≤ ε) →
      (∀ g e, a ≤ μ.real {x | code x = g} → |V g e - (Py e g.1 g.2.2).eval (g.2.1 : ℝ)| ≤ ε) →
      (∀ g e, a ≤ μ.real {x | code x = g} → |V g e - (Pz e g.1 g.2.1).eval (g.2.2 : ℝ)| ≤ ε) →
      ∃ (P : Fin q → MvPolynomial (Fin 3) ℝ) (G : Finset (S × S × S)),
        (∀ e, (P e).totalDegree ≤ 3 * D) ∧
        (∀ e d, |(P e).coeff d| ≤ C * (((D : ℝ) + 1) ^ 3 * B * ((1 + A) / r) ^ (3 * D))) ∧
        MeasurableSet {x | code x ∈ G} ∧
        (δ ^ ((D + 2) ^ 3) - 3 * ((D + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ))) / 2 *
          a * (S.card : ℝ) ^ 3 ≤ μ.real {x | code x ∈ G} ∧
        ∀ ω, code ω ∈ G → ∀ e,
          |V (code ω) e - eval (gridPoint (code ω)) (P e)| ≤
            3 * (1 + ((D : ℝ) + 1) * ((2 * A) / r) ^ D) ^ 3 * ε := by
  obtain ⟨C, hC, hcoef⟩ := exists_tensorPoly_coeff_bound D
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ S _ code hcode a U δ ξ r A B ε ha hU hδ hξ hr hB hε hA hsep hcap hbudget hgap
    V hVB Px Py Pz hPx hPy hPz hfx hfy hfz
  have hgap' : 3 * ((D + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ)) <
      δ ^ ((D + 1 + 1) ^ 3) := by simpa using hgap
  obtain ⟨xs, ys, zs, G, hanch, hheavy, hmass⟩ :=
    original_separated_grid_targets μ S code hcode a U δ ξ r ha hU hδ hξ hr hsep hcap hbudget
      (D + 1) hgap'
  have hsepx : ∀ i j, i ≠ j → r ≤ |(xs i : ℝ) - (xs j : ℝ)| := fun i j hij => hanch 0 i j hij
  have hsepy : ∀ i j, i ≠ j → r ≤ |(ys i : ℝ) - (ys j : ℝ)| := fun i j hij => hanch 1 i j hij
  have hsepz : ∀ i j, i ≠ j → r ≤ |(zs i : ℝ) - (zs j : ℝ)| := fun i j hij => hanch 2 i j hij
  have hAx : ∀ i, |(xs i : ℝ)| ≤ A := fun i => hA _ (xs i).2
  have hAy : ∀ i, |(ys i : ℝ)| ≤ A := fun i => hA _ (ys i).2
  have hAz : ∀ i, |(zs i : ℝ)| ≤ A := fun i => hA _ (zs i).2
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hAx 0)
  have hβ : 0 < (δ ^ ((D + 2) ^ 3) - 3 * ((D + 1 : ℕ) : ℝ) ^ 2 *
      ((2 * r / ξ + 1) / (S.card : ℝ))) / 2 * a * (S.card : ℝ) ^ 3 := by
    have hcard : (0 : ℝ) < S.card := by
      have : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_coe_sort.mp inferInstance)
      exact_mod_cast this
    have := sub_pos.mpr hgap
    positivity
  have hGne : G.Nonempty := by
    by_contra hG
    rw [Finset.not_nonempty_iff_eq_empty] at hG
    subst hG
    simp only [Finset.notMem_empty, Set.ofPred_false, measureReal_empty] at hmass
    linarith
  obtain ⟨g₀, hg₀⟩ := hGne
  have hVanchor : ∀ i j l e, |V (xs i, ys j, zs l) e| ≤ B := by
    intro i j l e
    apply hVB _ e
    have := hheavy g₀ hg₀ (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc l)
    simpa only [Fin.snoc_castSucc] using this
  refine ⟨fun e => tensorPoly (fun i => (xs i : ℝ)) (fun i => (ys i : ℝ)) (fun i => (zs i : ℝ))
      (fun i j l => V (xs i, ys j, zs l) e), G, fun e => totalDegree_tensorPoly_le _ _ _ _,
    fun e => hcoef _ _ _ A r B hr hA0 hB hAx hAy hAz hsepx hsepy hsepz _
      (fun i j l => hVanchor i j l e),
    hcode (Set.Finite.measurableSet (G.finite_toSet)), hmass, ?_⟩
  intro ω hω e
  exact grid_tensor_error D xs ys zs r A ε hr hε hA hanch
    (fun g => a ≤ μ.real {x | code x = g}) (code ω) (hheavy (code ω) hω)
    (fun g => V g e) (Px e) (Py e) (Pz e) (hPx e) (hPy e) (hPz e)
    (fun g hg => hfx g e hg) (fun g hg => hfy g e hg) (fun g hg => hfz g e hg)

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
