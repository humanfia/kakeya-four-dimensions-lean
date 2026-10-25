import Submission.Obl.k4_raw_localized_native_systems.Deletion.VelocityBins
import Submission.Obl.k4_uncapped_native_capping.UWE.AngularListMass

/- The finite-label organization and the diameter corollary are adapted from
this LOT tree o105, session x0548, commit6ab86148e24dd228044f997c2188e8d03c811f1b,
Submission/Obl/k4_critical_path_framework/ListedVelocityMass.lean. The measure
estimate imports the now accepted o214 angular-list theorem. -/

namespace Submission.Obl.k4_raw_localized_native_systems.Deletion

open MeasureTheory Set

noncomputable section

theorem listed_angular_support_mass_le {Ω X I β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] [Fintype β]
    (μ : Measure Ω) (ρ : Measure X) (f : Ω → X) (a : Ω → I)
    (hf : Measurable f) (ha : Measurable a)
    {g : X → ENNReal} {G : X × I → ENNReal} (hg : Measurable g) (hG : Measurable G)
    (hFine : μ.map f = ρ.withDensity g)
    (hJoint : μ.map (fun p => (f p, a p)) = (ρ.prod Measure.count).withDensity G)
    (F : β → Set Ω) (lst : X → Finset β)
    (hlist : ∀ b, MeasurableSet {x | b ∈ lst x})
    (B : β → Finset I) (m : ℕ) (κ : ℝ)
    (hcard : ∀ x, ((lst x).card : ℝ) ≤ κ)
    (hB : ∀ b, (B b).card ≤ m)
    (hknown : ∀ b p, p ∈ F b → b ∈ lst (f p))
    (hangle : ∀ b p, p ∈ F b → a p ∈ B b) (c : ENNReal) :
    μ (⋃ b, F b) ≤ μ {p | c * g (f p) < G (f p, a p)} +
      c * ENNReal.ofReal ((m : ℝ) * κ) * μ univ := by
  classical
  let L : X → Finset I := fun x => (lst x).biUnion B
  have hLm : MeasurableSet {p : X × I | p.2 ∈ L p.1} := by
    have heq : {p : X × I | p.2 ∈ L p.1} =
        ⋃ b : β, {x | b ∈ lst x} ×ˢ (B b : Set I) := by
      ext p
      simp only [L, Finset.mem_biUnion, mem_iUnion, mem_prod, Finset.mem_coe, Set.mem_ofPred_eq]
    rw [heq]
    exact MeasurableSet.iUnion fun b => (hlist b).prod ((B b).finite_toSet.measurableSet)
  have hLc (x : X) : ((L x).card : ENNReal) ≤ ENNReal.ofReal ((m : ℝ) * κ) := by
    have hc : ((L x).card : ℝ) ≤ (m : ℝ) * κ := by
      calc
        _ ≤ ((∑ b ∈ lst x, (B b).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ((∑ _b ∈ lst x, m : ℕ) : ℝ) := by
          exact_mod_cast Finset.sum_le_sum (fun b _ => hB b)
        _ = (m : ℝ) * ((lst x).card : ℝ) := by simp [mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcard x) (Nat.cast_nonneg m)
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hc
  let T : Set Ω := {p | a p ∈ L (f p) ∧ G (f p, a p) ≤ c * g (f p)}
  have hTm : MeasurableSet T :=
    (hLm.preimage (hf.prodMk ha)).inter
      (measurableSet_le (hG.comp (hf.prodMk ha)) (measurable_const.mul (hg.comp hf)))
  have hmass : μ T ≤ c * ENNReal.ofReal ((m : ℝ) * κ) * μ univ := by
    have h := Submission.Obl.k4_uncapped_native_capping.UWE.angular_list_mass_le
      μ (μ.restrict T) Measure.restrict_le_self ρ f hf a ha g hg G hG hFine hJoint
      c (ENNReal.ofReal ((m : ℝ) * κ)) univ MeasurableSet.univ L
      (fun i => (hLm.preimage (measurable_id.prodMk measurable_const))) hLc
      (by filter_upwards [ae_restrict_mem hTm] with p hp; exact ⟨mem_univ _, hp⟩)
    simpa only [Measure.restrict_apply_univ, preimage_univ] using h
  calc
    _ ≤ μ {p | c * g (f p) < G (f p, a p)} + μ T := by
      apply (measure_mono ?_).trans (measure_union_le _ _)
      intro p hp
      obtain ⟨b, hb⟩ := mem_iUnion.mp hp
      by_cases hcap : G (f p, a p) ≤ c * g (f p)
      · exact Or.inr ⟨Finset.mem_biUnion.mpr ⟨b, hknown b p hb, hangle b p hb⟩, hcap⟩
      · exact Or.inl (lt_of_not_ge hcap)
    _ ≤ _ := add_le_add le_rfl hmass

theorem listed_small_velocity_mass_le {Ω X β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Fintype β]
    (μ : Measure Ω) (ρ : Measure X) (f : Ω → X)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) {δ κ : ℝ} (hδ : 0 < δ)
    (hf : Measurable f) (hV : Measurable V)
    {g : X → ENNReal} {G : X × (Fin 2 → ℤ) → ENNReal}
    (hg : Measurable g) (hG : Measurable G)
    (hFine : μ.map f = ρ.withDensity g)
    (hJoint : μ.map (fun p => (f p, fun j => ⌊V p j / δ⌋)) =
      (ρ.prod Measure.count).withDensity G)
    (F : β → Set Ω) (lst : X → Finset β)
    (hlist : ∀ b, MeasurableSet {x | b ∈ lst x})
    (hcard : ∀ x, ((lst x).card : ℝ) ≤ κ)
    (hknown : ∀ b p, p ∈ F b → b ∈ lst (f p))
    (hdiam : ∀ b p, p ∈ F b → ∀ q, q ∈ F b → dist (V p) (V q) ≤ δ)
    (c : ENNReal) :
    μ (⋃ b, F b) ≤ μ {p | c * g (f p) < G (f p, fun j => ⌊V p j / δ⌋)} +
      c * ENNReal.ofReal (16 * κ) * μ univ := by
  classical
  have hbins (b : β) : ∃ B : Finset (Fin 2 → ℤ), B.card ≤ 16 ∧
      ∀ p ∈ F b, (fun j => ⌊V p j / δ⌋) ∈ B := by
    obtain ⟨B, hB, hmem⟩ := exists_angular_bins_of_diameter (V '' F b) hδ.le hδ (by
      rintro v ⟨p, hp, rfl⟩ w ⟨q, hq, rfl⟩
      exact hdiam b p hp q hq)
    have hfactor : 2 * δ / δ + 2 = (4 : ℝ) := by field_simp [hδ.ne'] <;> ring
    have hBc : (B.card : ℝ) ≤ 16 := by
      rw [hfactor] at hB
      norm_num at hB
      exact_mod_cast hB
    exact ⟨B, by exact_mod_cast hBc, fun p hp => hmem (V p) ⟨p, hp, rfl⟩⟩
  choose B hBc hBm using hbins
  exact listed_angular_support_mass_le μ ρ f (fun p j => ⌊V p j / δ⌋) hf
    (by fun_prop) hg hG hFine hJoint F lst hlist B 16 κ hcard hBc hknown hBm c

end
end Submission.Obl.k4_raw_localized_native_systems.Deletion
