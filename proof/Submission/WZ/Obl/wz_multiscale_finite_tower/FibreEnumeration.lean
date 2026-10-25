-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.FibreEnumeration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.IndexTransport

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound)

noncomputable def fibreEquiv {n m : ℕ} (p : Fin n → Fin m) (N : Fin m → ℕ)
    (e : ∀ k, Fin (N k) → Fin n) (hinj : ∀ k, Function.Injective (e k))
    (hrange : ∀ k, Set.range (e k) = {i | p i = k}) :
    (Σ k : Fin m, Fin (N k)) ≃ Fin n := by
  apply Equiv.ofBijective (fun a => e a.1 a.2)
  constructor
  · rintro ⟨k, a⟩ ⟨l, b⟩ he
    change e k a = e l b at he
    have hep (k) (a) : p (e k a) = k := by
      have hh : e k a ∈ Set.range (e k) := ⟨a, rfl⟩
      simpa only [hrange, Set.mem_setOf_eq] using hh
    have hkl : k = l := by rw [← hep k a, ← hep l b, he]
    subst l
    have hab : a = b := hinj k he
    subst b
    rfl
  · intro i
    have hi : i ∈ Set.range (e (p i)) := by rw [hrange]; rfl
    obtain ⟨a, ha⟩ := hi
    exact ⟨⟨p i, a⟩, ha⟩

lemma convexCount_injOn {n m : ℕ} {s L : ℝ} {P : Fin n → Prop} {Q : Fin m → Prop}
    {U : Fin n → Set Space} {V : Fin m → Set Space}
    (h : ConvexCount s L P U) (e : Fin m → Fin n)
    (he : Set.InjOn e {i | Q i}) (hP : ∀ i, Q i → P (e i))
    (hV : ∀ i, Q i → U (e i) = V i) : ConvexCount s L Q V := by
  intro W hW
  have hc : {i | Q i ∧ V i ⊆ W}.ncard ≤ {i | P i ∧ U i ⊆ W}.ncard :=
    Set.ncard_le_ncard_of_injOn e (fun i hi => ⟨hP i hi.1, by rw [hV i hi.1]; exact hi.2⟩)
      (fun a ha b hb h => he ha.1 hb.1 h)
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc)
    (sq_nonneg s))).trans (h W hW)

lemma slabBound_injOn {n m : ℕ} {L L' : ℝ} {D : Set Space}
    {P : Fin n → Prop} {Q : Fin m → Prop} {U : Fin n → Set Space} {V : Fin m → Set Space}
    (h : SlabBound D L P U) (e : Fin m → Fin n) (he : Set.InjOn e {i | Q i})
    (hP : ∀ i, Q i → P (e i)) (hV : ∀ i, Q i → U (e i) = V i)
    (hL : L * {i | P i}.ncard ≤ L' * {i | Q i}.ncard) : SlabBound D L' Q V := by
  intro u t r hu hr
  have hc : {i | Q i ∧ V i ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard ≤
      {i | P i ∧ U i ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard :=
    Set.ncard_le_ncard_of_injOn e (fun i hi => ⟨hP i hi.1, by rw [hV i hi.1]; exact hi.2⟩)
      (fun a ha b hb h => he ha.1 hb.1 h)
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl).trans
    ((h u t r hu hr).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl))

lemma image_geometry_ncard {n m : ℕ} {P : Fin n → Prop} {Q : Fin m → Prop}
    {U : Fin n → Set Space} {V : Fin m → Set Space}
    (e : Fin n → Fin m) (he : Function.Injective e) (hP : e '' {i | P i} = {i | Q i})
    (hV : ∀ i, P i → V (e i) = U i) (W : Set Space) :
    {i | Q i ∧ V i ⊆ W}.ncard = {i | P i ∧ U i ⊆ W}.ncard := by
  have hi : e '' {i | P i ∧ U i ⊆ W} = {i | Q i ∧ V i ⊆ W} := by
    ext j
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, by rw [hV i hi.1]; exact hi.2⟩
      have hh : e i ∈ e '' {i | P i} := ⟨i, hi.1, rfl⟩
      rwa [hP] at hh
    · rintro ⟨hj, hW⟩
      have hh : j ∈ e '' {i | P i} := by rw [hP]; exact hj
      obtain ⟨i, hi, rfl⟩ := hh
      exact ⟨i, ⟨hi, by rwa [hV i hi] at hW⟩, rfl⟩
  rw [← hi, Set.ncard_image_of_injective _ he]

lemma convexCount_image {n m : ℕ} {s L : ℝ} {P : Fin n → Prop} {Q : Fin m → Prop}
    {U : Fin n → Set Space} {V : Fin m → Set Space}
    (h : ConvexCount s L P U) (e : Fin n → Fin m) (he : Function.Injective e)
    (hP : e '' {i | P i} = {i | Q i}) (hV : ∀ i, P i → V (e i) = U i) :
    ConvexCount s L Q V := by
  intro W hW
  rw [image_geometry_ncard e he hP hV W]
  exact h W hW

lemma slabBound_image {n m : ℕ} {L : ℝ} {D : Set Space}
    {P : Fin n → Prop} {Q : Fin m → Prop} {U : Fin n → Set Space} {V : Fin m → Set Space}
    (h : SlabBound D L P U) (e : Fin n → Fin m) (he : Function.Injective e)
    (hP : e '' {i | P i} = {i | Q i}) (hV : ∀ i, P i → V (e i) = U i) :
    SlabBound D L Q V := by
  intro u t r hu hr
  rw [image_geometry_ncard e he hP hV, ← hP, Set.ncard_image_of_injective _ he]
  exact h u t r hu hr

end WangZahlLot.Obl.wz_multiscale_finite_tower
