-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FibreDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FactorDichotomy
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CanonicalFamily

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file FibreDichotomy.lean), namespace renamed.
/-!
# One o064 call per fibre

`fibre_dichotomy`: a fibre whose round boxes are not overfull is Katz–Tao after a `δ^ν`
refinement, otherwise it factors through flat saturated boxes.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
open Set MeasureTheory
open scoped ENNReal

/-- The `a × b × 2` box of the accepted convex factorization. -/
def factorBox (a b : ℝ) : Set Space := {y : Space | |y 0| ≤ a ∧ |y 1| ≤ b ∧ |y 2| ≤ 2}

/-- A finset of indices counted inside a set. -/
lemma card_filter_le_of_injOn {n k : ℕ} (F : Finset (Fin n)) (f : Fin k → Fin n)
    (hf : Function.Injective f) (hfF : ∀ j, f j ∈ F) (P : Fin n → Prop) [DecidablePred P] :
    ncard {j | P (f j)} ≤ (F.filter P).card := by
  classical
  rw [← Set.ncard_coe_finset]
  exact ncard_le_ncard_of_injOn f (fun j hj => by simpa [hfF j] using hj) hf.injOn

/-- A family of unit tubes, each of volume at least `δ²`, is trivially Katz–Tao with constant
equal to its size. -/
lemma katzTao_card {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (x v : Fin m → Space) (hv : ∀ i, ‖v i‖ = 1) :
    KatzTao δ (m : ℝ) (fun i => Tube δ (x i) (v i)) := by
  intro W hW
  rcases (({i | Tube δ (x i) (v i) ⊆ W} : Set (Fin m))).eq_empty_or_nonempty with h | ⟨i, hi⟩
  · rw [h, ncard_empty]; simp
  · have hvol : ENNReal.ofReal (δ ^ 2) ≤ volume W := by
      refine le_trans ?_ ((tube_volume_lower_box hδ (x i) (hv i)).trans (measure_mono hi))
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg δ])
    have hcard : (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤ m := by
      have := ncard_le_ncard (subset_univ {i | Tube δ (x i) (v i) ⊆ W})
      rw [ncard_univ, Nat.card_fin] at this
      exact_mod_cast this
    calc ENNReal.ofReal ((ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2)
        ≤ ENNReal.ofReal ((m : ℝ) * δ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (sq_nonneg δ))
      _ = ENNReal.ofReal m * ENNReal.ofReal (δ ^ 2) := ENNReal.ofReal_mul (Nat.cast_nonneg m)
      _ ≤ ENNReal.ofReal m * volume W := by gcongr

open Classical in
/-- **Per-fibre dichotomy** (one call of accepted o064 through x0210's `exists_long_factor`).
Let `F` be a nonempty set of tubes of an essentially distinct family of unit `δ`-tubes in the
unit ball. Suppose every `a × b × 2` box (any position, `δ ≤ a ≤ b ≤ Λ a`, `b ≤ 2`) holds at most
`K a b / δ²` tubes of `F`. Then either a `δ^ν` share `F'` of `F` is Katz–Tao with constant
`K δ^(-ν)` for all convex sets, or `F` has a flat saturated factorization with `b > Λ a`. -/
theorem fibre_dichotomy (ν : ℝ) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
      ∀ (n : ℕ) (x v : Fin n → Space), (∀ i, ‖v i‖ = 1) →
      (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) → Distinct (fun i => Tube δ (x i) (v i)) →
      ∀ (F : Finset (Fin n)), F.Nonempty → ∀ (K Λ : ℝ),
      (∀ (a b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space), δ ≤ a → a ≤ b → b ≤ Λ * a → b ≤ 2 →
        ((F.filter (fun i => Tube δ (x i) (v i) ⊆ e '' factorBox a b)).card : ℝ) * δ ^ 2 ≤
          K * a * b) →
      (∃ F' ⊆ F, (F.card : ℝ) ≤ δ ^ (-ν) * F'.card ∧ ∀ W : Set Space, Convex ℝ W →
          ENNReal.ofReal ((F'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card * δ ^ 2) ≤
            ENNReal.ofReal (K * δ ^ (-ν)) * volume W) ∨
      (∃ a b : ℝ, δ ≤ a ∧ Λ * a < b ∧ b ≤ 2 ∧
        LongFactor ν δ a b (fun j : Fin F.card =>
          Tube δ (x (F.equivFin.symm j)) (v (F.equivFin.symm j)))) := by
  classical
  obtain ⟨d, hd, hLF⟩ := exists_long_factor ν hν
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδ100 hδd n x v hv hball hsep F hF K Λ hround
  set m := F.card with hm
  let e : Fin m ≃ F := F.equivFin.symm
  let xF : Fin m → Space := fun j => x (e j)
  let vF : Fin m → Space := fun j => v (e j)
  have hm0 : 0 < m := Finset.card_pos.mpr hF
  have he : Function.Injective (fun j : Fin m => (e j : Fin n)) :=
    fun a b h => e.injective (Subtype.ext h)
  have heF : ∀ j, (e j : Fin n) ∈ F := fun j => (e j).2
  obtain ⟨a, b, hδa, hab, hb2, hfac⟩ := hLF δ hδ hδ100 hδd (m : ℝ)
    (by exact_mod_cast hm0) m xF vF hm0 (fun j => hv _) (fun j => hball _)
    (fun i j hij => hsep _ _ (he.ne hij)) (katzTao_card hδ xF vF (fun j => hv _))
  by_cases hflat : Λ * a < b
  · exact Or.inr ⟨a, b, hδa, hflat, hb2, hfac⟩
  left
  have hround' : b ≤ Λ * a := not_lt.mp hflat
  obtain ⟨k, g, hg, hk, hsize, c, hc1, hKTc, p, W, hshape, hcover, hdeg, hsat⟩ := hfac
  obtain ⟨j₀, hj₀⟩ := hcover ⟨0, hk⟩
  obtain ⟨e₀, he₀⟩ := hshape j₀
  -- saturation of `W j₀` against the round-box bound
  have hcont : (contained (fun i => Tube δ (xF (g i)) (vF (g i))) (W j₀) : ℝ) ≤
      (F.filter (fun i => Tube δ (x i) (v i) ⊆ e₀ '' factorBox a b)).card := by
    unfold contained
    have := card_filter_le_of_injOn F (fun i => (e (g i) : Fin n))
      (he.comp hg) (fun i => heF _) (fun i => Tube δ (x i) (v i) ⊆ e₀ '' factorBox a b)
    rw [he₀] at *
    exact_mod_cast this
  have hround₀ := hround a b e₀ hδa hab hround' hb2
  have ha0 : 0 < a := hδ.trans_le hδa
  have hb0 : 0 < b := ha0.trans_le hab
  have hcK : c ≤ K * δ ^ (-ν) := by
    have h1 : δ ^ ν * c * a * b ≤ K * a * b := by
      calc δ ^ ν * c * a * b ≤ _ := hsat j₀
        _ ≤ _ := mul_le_mul_of_nonneg_right hcont (sq_nonneg δ)
        _ ≤ K * a * b := hround₀
    have hab0 : 0 < a * b := mul_pos ha0 hb0
    have h2 : δ ^ ν * c ≤ K := by
      have : (δ ^ ν * c) * (a * b) ≤ K * (a * b) := by nlinarith
      exact le_of_mul_le_mul_right this hab0
    have hpos : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ ν
    calc c = δ ^ (-ν) * (δ ^ ν * c) := by
          rw [← mul_assoc, ← Real.rpow_add hδ]; simp
      _ ≤ δ ^ (-ν) * K := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hδ.le _)
      _ = K * δ ^ (-ν) := by ring
  -- the kept subfamily as a finset of original indices
  let F' : Finset (Fin n) := Finset.univ.image (fun i : Fin k => (e (g i) : Fin n))
  have hF'sub : F' ⊆ F := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact heF _
  have hinj : Function.Injective (fun i : Fin k => (e (g i) : Fin n)) := he.comp hg
  have hF'card : F'.card = k := by
    simp only [F']
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  refine ⟨F', hF'sub, ?_, ?_⟩
  · rw [hF'card]
    have hpos : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ ν
    have h := hsize
    calc (m : ℝ) = δ ^ (-ν) * (δ ^ ν * m) := by
          rw [← mul_assoc, ← Real.rpow_add hδ]; simp
      _ ≤ δ ^ (-ν) * k := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hδ.le _)
  · intro U hU
    have hsetEq : (F'.filter (fun i => Tube δ (x i) (v i) ⊆ U)).card =
        ncard {i : Fin k | Tube δ (xF (g i)) (vF (g i)) ⊆ U} := by
      rw [← Set.ncard_coe_finset]
      have himg : (↑(F'.filter (fun i => Tube δ (x i) (v i) ⊆ U)) : Set (Fin n)) =
          (fun i : Fin k => (e (g i) : Fin n)) '' {i | Tube δ (xF (g i)) (vF (g i)) ⊆ U} := by
        ext i
        simp only [Finset.coe_filter, mem_ofPred_eq, mem_image, F', Finset.mem_image,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨j, rfl⟩, hj⟩; exact ⟨j, hj, rfl⟩
        · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, rfl⟩, hj⟩
      rw [himg, ncard_image_of_injective _ hinj]
    rw [hsetEq]
    calc ENNReal.ofReal ((ncard {i : Fin k | Tube δ (xF (g i)) (vF (g i)) ⊆ U} : ℝ) * δ ^ 2)
        ≤ ENNReal.ofReal c * volume U := hKTc U hU
      _ ≤ ENNReal.ofReal (K * δ ^ (-ν)) * volume U := by
          gcongr

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
