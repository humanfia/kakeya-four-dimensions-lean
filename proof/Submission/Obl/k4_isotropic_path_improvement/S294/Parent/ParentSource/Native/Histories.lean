-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.Histories, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/Histories.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/Histories.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/Histories.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/Histories.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path

/-! Finite measurable histories for supplied packet families. Encoding all
memberships avoids choosing representatives on shared closed time endpoints. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set

noncomputable def finitePacketHistory {W C : ℕ} {X : Type*}
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X)
    (i : ℕ) (z : Fin W × X) : ℕ := by
  classical
  exact Encodable.encode (z.1,
    fun b => decide (lev b ≤ i ∧ γ b = z.1 ∧ z.2 ∈ F b))

theorem measurable_finitePacketHistory {W C : ℕ} {X : Type*} [MeasurableSpace X]
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X)
    (hF : ∀ b, MeasurableSet (F b)) (i : ℕ) :
    Measurable (finitePacketHistory lev γ F i) := by
  classical
  apply (measurable_of_countable Encodable.encode).comp
  apply measurable_fst.prodMk
  apply Measurable.of_eval
  intro b
  have hset : MeasurableSet {z : Fin W × X | lev b ≤ i ∧ γ b = z.1 ∧ z.2 ∈ F b} := by
    by_cases hbi : lev b ≤ i
    · simp only [hbi, true_and]
      exact (measurableSet_eq_fun measurable_const measurable_fst).inter
        ((hF b).preimage measurable_snd)
    · simp only [hbi, false_and, Set.ofPred_false]
      exact MeasurableSet.empty
  have heq : (fun z : Fin W × X => decide (lev b ≤ i ∧ γ b = z.1 ∧ z.2 ∈ F b)) =
      {z : Fin W × X | lev b ≤ i ∧ γ b = z.1 ∧ z.2 ∈ F b}.piecewise
        (fun _ => true) (fun _ => false) := by
    funext z
    by_cases hz : lev b ≤ i ∧ γ b = z.1 ∧ z.2 ∈ F b <;> simp [hz]
  rw [heq]
  exact measurable_const.piecewise hset measurable_const

theorem finite_finitePacketHistory_range {W C : ℕ} {X : Type*}
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (i : ℕ) :
    (Set.range (finitePacketHistory lev γ F i)).Finite := by
  classical
  apply (Set.finite_range (Encodable.encode : Fin W × (Fin C → Bool) → ℕ)).subset
  rintro _ ⟨z, rfl⟩
  exact ⟨_, rfl⟩

theorem finitePacketHistory_nested {W C : ℕ} {X : Type*}
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X)
    {i j : ℕ} (hij : i ≤ j) {z z' : Fin W × X}
    (h : finitePacketHistory lev γ F j z = finitePacketHistory lev γ F j z') :
    finitePacketHistory lev γ F i z = finitePacketHistory lev γ F i z' := by
  classical
  have hdec := Encodable.encode_injective h
  have hw := congrArg (fun x : Fin W × (Fin C → Bool) => x.1) hdec
  apply congrArg Encodable.encode
  apply Prod.ext
  · exact hw
  funext b
  by_cases hbi : lev b ≤ i
  · have hbj : lev b ≤ j := hbi.trans hij
    simpa only [hbi, hbj, true_and] using congrArg (fun x => x.2 b) hdec
  · simp only [hbi, false_and, decide_false]

/-- Equal histories retain the world and every packet membership already seen. -/
theorem finitePacketHistory_eq_mem {W C : ℕ} {X : Type*}
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X)
    {i : ℕ} {z z' : Fin W × X}
    (h : finitePacketHistory lev γ F i z = finitePacketHistory lev γ F i z') :
    z.1 = z'.1 ∧ ∀ b, lev b ≤ i → γ b = z.1 → (z.2 ∈ F b ↔ z'.2 ∈ F b) := by
  classical
  have hdec := Encodable.encode_injective h
  have hw : z.1 = z'.1 := congrArg (fun x : Fin W × (Fin C → Bool) => x.1) hdec
  refine ⟨hw, ?_⟩
  intro b hbi hγ
  have hb := congrArg (fun x => x.2 b) hdec
  simpa only [hbi, hγ, ← hw, true_and, decide_eq_decide] using hb

def packetUnique {W C : ℕ} {X : Type*} (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (F : Fin C → Set X) (w : Fin W) (x : X) : Prop :=
  ∀ b b', lev b = lev b' → γ b = w → γ b' = w → x ∈ F b → x ∈ F b' → b = b'

/-- In a nested family, an occupied packet determines its entire old history
at points where no two packets of the same level and world overlap. -/
theorem finitePacketHistory_eq_on_packet {W C : ℕ} {X : Type*}
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (b : Fin C)
    (hAnc : ∀ i, i ≤ lev b → ∃ a, lev a = i ∧ γ a = γ b ∧ F b ⊆ F a)
    {x y : X} (hx : x ∈ F b) (hy : y ∈ F b)
    (hux : packetUnique lev γ F (γ b) x) (huy : packetUnique lev γ F (γ b) y) :
    finitePacketHistory lev γ F (lev b) (γ b, x) =
      finitePacketHistory lev γ F (lev b) (γ b, y) := by
  classical
  have hmem (x y : X) (hx : x ∈ F b) (hy : y ∈ F b)
      (hu : packetUnique lev γ F (γ b) x) (a : Fin C)
      (ha : lev a ≤ lev b) (hγ : γ a = γ b) (hax : x ∈ F a) : y ∈ F a := by
    obtain ⟨c, hci, hcγ, hFc⟩ := hAnc (lev a) ha
    have heq : a = c := hu a c hci.symm hγ hcγ hax (hFc hx)
    simpa only [heq] using hFc hy
  unfold finitePacketHistory
  apply congrArg Encodable.encode
  apply Prod.ext
  · rfl
  funext a
  by_cases ha : lev a ≤ lev b
  · by_cases hγ : γ a = γ b
    · have hiff : x ∈ F a ↔ y ∈ F a :=
        ⟨hmem x y hx hy hux a ha hγ, hmem y x hy hx huy a ha hγ⟩
      simpa only [ha, hγ, true_and, decide_eq_decide] using hiff
    · simp only [ha, hγ, true_and, false_and, decide_false]
  · simp only [ha, false_and, decide_false]

theorem finitePacketHistory_fiber_eq_packet {W C : ℕ} {X : Type*}
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (b : Fin C)
    (hAnc : ∀ i, i ≤ lev b → ∃ a, lev a = i ∧ γ a = γ b ∧ F b ⊆ F a)
    {x : X} (hx : x ∈ F b) (hux : packetUnique lev γ F (γ b) x) :
    {y | packetUnique lev γ F (γ b) y ∧
      finitePacketHistory lev γ F (lev b) (γ b, y) =
        finitePacketHistory lev γ F (lev b) (γ b, x)} =
      {y | packetUnique lev γ F (γ b) y ∧ y ∈ F b} := by
  ext y
  constructor
  · rintro ⟨huy, hhist⟩
    have hmem := (finitePacketHistory_eq_mem lev γ F hhist).2 b le_rfl rfl
    exact ⟨huy, hmem.mpr hx⟩
  · rintro ⟨huy, hy⟩
    exact ⟨huy, finitePacketHistory_eq_on_packet lev γ F b hAnc hy hx huy hux⟩

/-- A finite same-level a.e. disjoint family has unique memberships off one
null set, simultaneously over every level. -/
theorem ae_packetUnique {W C : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (w : Fin W)
    (hdisj : ∀ b b', b ≠ b' → lev b = lev b' → γ b = w → γ b' = w →
      AEDisjoint μ (F b) (F b')) :
    ∀ᵐ x ∂μ, packetUnique lev γ F w x := by
  classical
  change ∀ᵐ x ∂μ, ∀ b b', lev b = lev b' → γ b = w → γ b' = w →
    x ∈ F b → x ∈ F b' → b = b'
  apply ae_all_iff.mpr
  intro b
  apply ae_all_iff.mpr
  intro b'
  by_cases heq : b = b'
  · exact Filter.Eventually.of_forall (fun _ _ _ _ _ _ => heq)
  by_cases hc : lev b = lev b' ∧ γ b = w ∧ γ b' = w
  · have hd := hdisj b b' heq hc.1 hc.2.1 hc.2.2
    have hnull : μ {x | x ∈ F b ∧ x ∈ F b'} = 0 := hd
    have hae : ∀ᵐ x ∂μ, ¬ (x ∈ F b ∧ x ∈ F b') :=
      ae_iff.mpr (by simpa only [not_not] using hnull)
    filter_upwards [hae] with x hx
    intro _ _ _ hxb hxb'
    exact False.elim (hx ⟨hxb, hxb'⟩)
  · exact Filter.Eventually.of_forall (fun _ hl hγ hγ' _ _ => False.elim (hc ⟨hl, hγ, hγ'⟩))

/-- Every positive packet in a finite nested a.e. disjoint family has one
history code, fixed independently of all future residual omissions. -/
theorem exists_history_code_of_packet {W C : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (b : Fin C)
    (hAnc : ∀ i, i ≤ lev b → ∃ a, lev a = i ∧ γ a = γ b ∧ F b ⊆ F a)
    (hdisj : ∀ a a', a ≠ a' → lev a = lev a' → γ a = γ b → γ a' = γ b →
      AEDisjoint μ (F a) (F a')) (hpos : 0 < μ (F b)) :
    ∃ code : ℕ, ∀ᵐ y ∂μ,
      finitePacketHistory lev γ F (lev b) (γ b, y) = code ↔ y ∈ F b := by
  classical
  have hUnique := ae_packetUnique μ lev γ F (γ b) hdisj
  have hex : ∃ x, x ∈ F b ∧ packetUnique lev γ F (γ b) x := by
    by_contra hnone
    have hsub : F b ⊆ {x | ¬ packetUnique lev γ F (γ b) x} := by
      intro x hx hux
      exact hnone ⟨x, hx, hux⟩
    have hzero := measure_mono_null hsub (ae_iff.mp hUnique)
    exact hpos.ne' hzero
  obtain ⟨x, hx, hux⟩ := hex
  refine ⟨finitePacketHistory lev γ F (lev b) (γ b, x), ?_⟩
  filter_upwards [hUnique] with y huy
  constructor
  · intro hhist
    exact ((finitePacketHistory_eq_mem lev γ F hhist).2 b le_rfl rfl).mpr hx
  · intro hy
    exact finitePacketHistory_eq_on_packet lev γ F b hAnc hy hx huy hux

/-- A fixed history code identifies the same original conditional law as the
packet, after ANY future incidence restriction. -/
theorem cond_eq_packet_of_history_code {W C : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (b : Fin C)
    (code : ℕ) (hcode : ∀ᵐ y ∂μ,
      finitePacketHistory lev γ F (lev b) (γ b, y) = code ↔ y ∈ F b) (H : Set X) :
    ProbabilityTheory.cond μ (H ∩ {y | finitePacketHistory lev γ F (lev b) (γ b, y) = code}) =
      ProbabilityTheory.cond μ (H ∩ F b) := by
  have heq : H ∩ {y | finitePacketHistory lev γ F (lev b) (γ b, y) = code} =ᵐ[μ] H ∩ F b := by
    filter_upwards [hcode] with y hy
    simp only [mem_inter_iff, mem_ofPred_eq, hy]
  simp only [ProbabilityTheory.cond, measure_congr heq, Measure.restrict_congr_set heq]

/-- A positive packet contains an actual point carrying its a.e. fixed code. -/
theorem exists_point_of_packet_code {W C : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (b : Fin C)
    (code : ℕ) (hcode : ∀ᵐ y ∂μ,
      finitePacketHistory lev γ F (lev b) (γ b, y) = code ↔ y ∈ F b)
    (hpos : 0 < μ (F b)) :
    ∃ x, x ∈ F b ∧ finitePacketHistory lev γ F (lev b) (γ b, x) = code := by
  by_contra hnone
  have hsub : F b ⊆ {x | ¬ (finitePacketHistory lev γ F (lev b) (γ b, x) = code ↔ x ∈ F b)} := by
    intro x hx hc
    exact hnone ⟨x, hx, hc.mpr hx⟩
  exact hpos.ne' (measure_mono_null hsub (ae_iff.mp hcode))

/-- A code representing a positive old packet belongs to exactly its world,
even at points outside the support of the original measure. -/
theorem finitePacketHistory_world_of_packet_code {W C : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (b : Fin C)
    (code : ℕ) (hcode : ∀ᵐ y ∂μ,
      finitePacketHistory lev γ F (lev b) (γ b, y) = code ↔ y ∈ F b)
    (hpos : 0 < μ (F b)) :
    ∀ z, finitePacketHistory lev γ F (lev b) z = code → z.1 = γ b := by
  obtain ⟨x, _, hx⟩ := exists_point_of_packet_code μ lev γ F b code hcode hpos
  intro z hz
  exact (finitePacketHistory_eq_mem lev γ F (hz.trans hx.symm)).1

/-- The fixed code fiber is pointwise inside the packet. The reverse
inclusion only needs to hold a.e. to handle shared closed time endpoints. -/
theorem finitePacketHistory_packet_of_packet_code {W C : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set X) (b : Fin C)
    (code : ℕ) (hcode : ∀ᵐ y ∂μ,
      finitePacketHistory lev γ F (lev b) (γ b, y) = code ↔ y ∈ F b)
    (hpos : 0 < μ (F b)) :
    ∀ z, finitePacketHistory lev γ F (lev b) z = code → z.1 = γ b ∧ z.2 ∈ F b := by
  obtain ⟨x, hxF, hx⟩ := exists_point_of_packet_code μ lev γ F b code hcode hpos
  intro z hz
  have he := finitePacketHistory_eq_mem lev γ F (hz.trans hx.symm)
  exact ⟨he.1, (he.2 b le_rfl he.1.symm).mpr hxF⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
