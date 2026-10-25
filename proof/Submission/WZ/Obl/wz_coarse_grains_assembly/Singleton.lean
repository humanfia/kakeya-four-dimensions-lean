-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.Singleton.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.UnitCarrier
import Submission.WZ.Obl.wz_coarse_grains_assembly.LocalCount
import Submission.WZ.Obl.wz_coarse_grains_assembly.Mono

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- Global broadness is the broadness of the one-member coarse family. -/
theorem broad_singleton_of_global {ω ζ δ h ρ : ℝ} {n : ℕ}
    {v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    (hzero : ∀ i, i ∉ S → Z i = ∅)
    (hbr : ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ Z i}) :
    Broad ω ζ δ h ρ n 1 v S Z (fun _ => 0) := by
  have hmem (p : V) (i : Fin n) (hi : p ∈ Z i) : i ∈ S := by
    by_contra hn
    rw [hzero i hn] at hi
    exact hi
  have he (k : Fin 1) (p : V) (P : Fin n → Prop) :
      {i | i ∈ S ∧ (0 : Fin 1) = k ∧ p ∈ Z i ∧ P i} = {i | p ∈ Z i ∧ P i} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun hi => hi.2.2, fun hi => ⟨hmem p i hi.1, Subsingleton.elim _ _, hi⟩⟩
  have he' (k : Fin 1) (p : V) :
      {i | i ∈ S ∧ (0 : Fin 1) = k ∧ p ∈ Z i} = {i | p ∈ Z i} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun hi => hi.2.2, fun hi => ⟨hmem p i hi, Subsingleton.elim _ _, hi⟩⟩
  intro k p u r hu hdr hrρ
  simpa only [he, he'] using hbr p u r hu hdr hrρ

/-- At radius one, the one-member coarse family satisfies the cover
conditions as soon as containment and retained mass are available. -/
theorem singleton_unit_cover {δ h : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {y w : V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h)
    (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅))
    (hmass : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i))
    (hw : ‖w‖ = 1) (hT : ∀ i ∈ S, T δ (x i) (v i) ⊆ T 1 y w) :
    C δ h n x v Y S Z 1 1 (fun _ => y) (fun _ => w) (fun _ => 0) True := by
  have hone : 1 ≤ δ ^ (-h) := by
    simpa only [neg_zero, Real.rpow_zero] using (rpow_err_le hδ hδ1 hh).2
  refine ⟨hZ, hmass, fun _ => hw, hT, unit_radius_frostman _ _ (fun _ => hw) _,
    True.intro, ?_, ?_, ?_⟩
  · intro k k'
    have he : k = k' := Subsingleton.elim _ _
    subst k'
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hone
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · intro i hi
    calc
      _ ≤ q 1 Set.univ := Nat.cast_le.mpr
        (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _))
      _ = 1 := by simp [q]
      _ ≤ δ ^ (-h) := hone

/-- A single-tube grains output gives the frozen `H` predicate, with the
finite local convex-count coefficient supplied by the box volumes. -/
theorem singleton_grains_of_boxes {δ h ρ a c : ℝ} {n L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V} {y w : V}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {G : Fin L → Set V} {m : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (ha : a ≤ ρ * c) (hrc : ρ * c ≤ c) (hc1 : c ≤ 1)
    (hzero : ∀ i, i ∉ S → Z i = ∅)
    (hgeom : ∀ j, MeasurableSet (G j) ∧ G j ⊆ P a (ρ*c) c (z j) (e j) ∧
      P a (ρ*c) c (z j) (e j) ⊆ T ρ y w ∧
      ι (e j w) 0 ^ 2 + ι (e j w) 1 ^ 2 ≤ (10*ρ)^2)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (G j) (G j'))
    (hunion : {p | ∃ j, p ∈ G j} = {p | ∃ i, p ∈ Z i})
    (hmass : O (δ ^ h * L * a * (ρ*c) * c) ≤ ∑ j, μ (G j))
    (hmult : ∀ p, (∃ i, p ∈ Z i) → q n {i | p ∈ Z i} ∈ Set.Icc m (2*m))
    (hcross : ∀ i j, (Z i ∩ G j).Nonempty →
      Z i ∩ P a (ρ*c) c (z j) (e j) ⊆ G j ∧
      (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a (ρ*c) c (z j) (e j)),
        abs (ι (e j (p-z j)) 2) = c/2) ∧
      ∀ t ∈ ({-c/2,c/2} : Set ℝ), ∃ p ∈ T δ (x i) (v i) ∩ P a (ρ*c) c (z j) (e j),
        ι (e j (p-z j)) 2 = t) :
    H δ h n x v S Z ρ 1 (fun _ => y) (fun _ => w) (fun _ => 0) a c 0 (max 1 L) := by
  have hmem (p : V) (i : Fin n) (hi : p ∈ Z i) : i ∈ S := by
    by_contra hn
    rw [hzero i hn] at hi
    exact hi
  have ha0 : 0 ≤ a := hδ.le.trans hδa
  have hrc0 : 0 ≤ ρ * c := ha0.trans ha
  have hc0 : 0 ≤ c := hrc0.trans hrc
  refine ⟨L, z, e, G, (fun _ => 0), m, hδa, ha, hrc, hc1, hgeom,
    (fun j j' hne _ => hdisj j j' hne), ?_, hmass, ?_, ?_, hc0, ?_⟩
  · intro k
    ext p
    have hu : (∃ j, p ∈ G j) ↔ ∃ i, p ∈ Z i := by
      exact Set.ext_iff.mp hunion p
    change (∃ j, (0 : Fin 1) = k ∧ p ∈ G j) ↔ ∃ i ∈ S, (0 : Fin 1) = k ∧ p ∈ Z i
    constructor
    · rintro ⟨j, _, hj⟩
      obtain ⟨i, hi⟩ := hu.mp ⟨j, hj⟩
      exact ⟨i, hmem p i hi, Subsingleton.elim _ _, hi⟩
    · rintro ⟨i, _, _, hi⟩
      obtain ⟨j, hj⟩ := hu.mpr ⟨i, hi⟩
      exact ⟨j, Subsingleton.elim _ _, hj⟩
  · intro k p hp
    have he : {i | i ∈ S ∧ (0 : Fin 1) = k ∧ p ∈ Z i} = {i | p ∈ Z i} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun hi => hi.2.2, fun hi => ⟨hmem p i hi, Subsingleton.elim _ _, hi⟩⟩
    rw [he]
    obtain ⟨i, _, _, hi⟩ := hp
    exact hmult p ⟨i, hi⟩
  · exact fun i _ j _ hij => hcross i j hij
  · exact local_count_of_le ha0 hrc0 hc0 z e (le_max_right _ _)

end WangZahlLot.Obl.wz_coarse_grains_assembly
