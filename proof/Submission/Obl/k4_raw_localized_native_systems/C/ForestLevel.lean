import Submission.Obl.k4_raw_localized_native_systems.C.NestedSources
import Submission.Obl.k4_raw_localized_native_systems.C.CQ1Compare
import Submission.Obl.k4_raw_localized_native_systems.C.Q2Path

/-
Adapted from this LOT tree, o178, session x0596, `ForestLevel.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# One level of a nested forest as a chart system

The nodes of one level of a raw forest (accepted o192 `Forest`) form an o153
`Atlas` with the same time exponent, worlds, blocks, frames, tests, full
assignments and selected incidences.  Under the forest's core predicate it is a
true chart system at the level's depth (chart predicate with the incidence floor,
disjointness within worlds and blocks, coverage), and the own-depth lists of a
prepared forest give lists by the terminal observation (through the coarsening of
observations) which can be chosen measurable with the same length bound
(`measurable_decoder_of_source_images`).
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests

noncomputable section

variable {p : Data} {k : ℕ}

/-- The nodes of one level. -/
def levelSet (a : Forest p k) (i : ℕ) : Finset (Fin a.C) := by
  classical
  exact Finset.univ.filter (fun b => a.lev b = i)

/-- The embedding of the level, re-indexed. -/
def levelEmb (a : Forest p k) (i : ℕ) (c : Fin (levelSet a i).card) : Fin a.C :=
  ((levelSet a i).equivFin.symm c).1

theorem levelEmb_lev (a : Forest p k) (i : ℕ) (c : Fin (levelSet a i).card) :
    a.lev (levelEmb a i c) = i := by
  classical
  have := ((levelSet a i).equivFin.symm c).2
  simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

theorem levelEmb_injective (a : Forest p k) (i : ℕ) : Function.Injective (levelEmb a i) := by
  intro c c' h
  exact (levelSet a i).equivFin.symm.injective (Subtype.ext h)

/-- Every node of the level is an embedded index. -/
theorem levelEmb_surj (a : Forest p k) {i : ℕ} {b : Fin a.C} (hb : a.lev b = i) :
    ∃ c, levelEmb a i c = b := by
  classical
  have hmem : b ∈ levelSet a i := by
    simp [levelSet, hb]
  refine ⟨(levelSet a i).equivFin ⟨b, hmem⟩, ?_⟩
  simp [levelEmb]

/-- The level as a chart system. -/
def levelAtlas (a : Forest p k) (i : ℕ)
    (lst : Fin (p.W k) → Observation → Finset (Fin (levelSet a i).card)) : Atlas p k where
  T := a.T i
  C := (levelSet a i).card
  γ c := a.γ (levelEmb a i c)
  j c := if h : a.j (levelEmb a i c) < 2 ^ a.T i then ⟨a.j (levelEmb a i c), h⟩
    else ⟨0, Nat.pos_of_ne_zero (pow_ne_zero _ two_ne_zero)⟩
  c c := a.c (levelEmb a i c)
  u c := a.u (levelEmb a i c)
  Q c := a.Q (levelEmb a i c)
  R c := a.R (levelEmb a i c)
  A c := a.A (levelEmb a i c)
  F c := a.F (levelEmb a i c)
  lst := lst

section core

variable {a : Forest p k} {M D m : ℕ} {r : ℕ → ℝ} (hcore : a.Core M D m r) {i : ℕ}
  (him : i < m) (lst : Fin (p.W k) → Observation → Finset (Fin (levelSet a i).card))

include hcore him

theorem levelAtlas_j (c : Fin (levelSet a i).card) :
    (((levelAtlas a i lst).j c : ℕ) : ℝ) = (a.j (levelEmb a i c) : ℝ) := by
  have h := (hcore.2.2.2.2.2 (levelEmb a i c)).2.1
  rw [levelEmb_lev a i c] at h
  simp [levelAtlas, h]

/-- **The level is a true chart system at its depth.** -/
theorem levelAtlas_charts :
    ChartsHyp (levelAtlas a i lst) M D a.κ (r i) (fun c =>
      ENNReal.ofReal (p.N k ^ (-p.f (r i)) * |Matrix.det (a.Q (levelEmb a i c))| /
        ((2 : ℝ) ^ a.T i * a.κ)) ≤ priorMass p k (a.γ (levelEmb a i c)) (a.F (levelEmb a i c))) := by
  intro c
  have h := (hcore.2.2.2.2.2 (levelEmb a i c)).2.2.1
  rw [levelEmb_lev a i c] at h
  rw [levelAtlas_j hcore him lst c]
  exact h

theorem levelAtlas_disjoint :
    ∀ c c', c ≠ c' → (levelAtlas a i lst).γ c = (levelAtlas a i lst).γ c' →
      (levelAtlas a i lst).j c = (levelAtlas a i lst).j c' →
      Disjoint ((levelAtlas a i lst).A c) ((levelAtlas a i lst).A c') := by
  intro c c' hne hγ hj
  have hj' : a.j (levelEmb a i c) = a.j (levelEmb a i c') := by
    have h1 := levelAtlas_j hcore him lst c
    have h2 := levelAtlas_j hcore him lst c'
    rw [hj] at h1
    exact_mod_cast h1.symm.trans h2
  exact hcore.2.2.2.2.1 _ _ (fun h => hne (levelEmb_injective a i h))
    ((levelEmb_lev a i c).trans (levelEmb_lev a i c').symm) hγ hj'

theorem levelAtlas_floor (c : Fin (levelAtlas a i lst).C) :
    ENNReal.ofReal (p.N k ^ (-p.f (r i)) * |((levelAtlas a i lst).Q c).det| /
      ((2 : ℝ) ^ (levelAtlas a i lst).T * a.κ)) ≤
        priorMass p k ((levelAtlas a i lst).γ c) ((levelAtlas a i lst).F c) :=
  (levelAtlas_charts hcore him lst c).2.2.2.2.2.2.2.2.2.2.2

/-- **Coverage of the level.** -/
theorem levelAtlas_coverage :
    ENNReal.ofReal a.κ⁻¹ ≤ ∑ c, ENNReal.ofReal (p.ω k ((levelAtlas a i lst).γ c)) *
      priorMass p k ((levelAtlas a i lst).γ c) ((levelAtlas a i lst).F c) := by
  classical
  have h := hcore.2.2.2.1 i him
  refine h.trans (le_of_eq ?_)
  rw [← Finset.sum_filter]
  change ∑ b ∈ levelSet a i, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b) = _
  rw [← Finset.sum_coe_sort (levelSet a i)]
  exact Fintype.sum_equiv (levelSet a i).equivFin _ _ (fun b => by simp [levelAtlas, levelEmb])

end core

/-- **Measurable terminal lists of a level.** The own-depth lists of a prepared forest,
restricted to the level, factor through the terminal observation and can be chosen
measurable with the same length bound. -/
theorem exists_level_lists (hp : Valid p) {a : Forest p k} {M D m : ℕ} {r : ℕ → ℝ}
    (hcore : a.Core M D m r) {i : ℕ} (him : i < m) (hr0 : 0 ≤ r i) (hrL : r i ≤ p.L)
    {lstF : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)} (hprep : a.Prepared r lstF) :
    ∃ Λ : Fin (p.W k) → Observation → Finset (Fin (levelSet a i).card),
      (∀ γ c, MeasurableSet {o | c ∈ Λ γ o}) ∧ (∀ γ o, ((Λ γ o).card : ℝ) ≤ a.κ) ∧
      ∀ c, ∀ z ∈ a.F (levelEmb a i c),
        c ∈ Λ (a.γ (levelEmb a i c)) (obs (p.B k (a.γ (levelEmb a i c))) (δ (p.N k) p.L) z) := by
  classical
  have hN1 : 1 ≤ p.N k := hp.scale_ge_one k
  set n := Submission.Lib.K4XInterface.depthIdx (p.N k) p.L -
    Submission.Lib.K4XInterface.depthIdx (p.N k) (r i) with hn
  -- the level lists by the terminal observation
  let L : Fin (p.W k) → Observation → Finset (Fin (levelSet a i).card) := fun γ o =>
    Finset.univ.filter (fun c => levelEmb a i c ∈ lstF i γ
      (Submission.Lib.K4XInterface.coarsenObs n o))
  have hLcard : ∀ γ o, ((L γ o).card : ℝ) ≤ a.κ := by
    intro γ o
    have hsub : (L γ o).map ⟨levelEmb a i, levelEmb_injective a i⟩ ⊆
        lstF i γ (Submission.Lib.K4XInterface.coarsenObs n o) := by
      intro b hb
      rw [Finset.mem_map] at hb
      obtain ⟨c, hc, rfl⟩ := hb
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hc
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_map] at h1
    exact (Nat.cast_le.2 h1).trans (hprep.1 i γ _)
  have hknown : ∀ c, ∀ z ∈ a.F (levelEmb a i c),
      c ∈ L (a.γ (levelEmb a i c)) (obs (p.B k (a.γ (levelEmb a i c))) (δ (p.N k) p.L) z) := by
    intro c z hz
    have h := (hprep.2 (levelEmb a i c)).2 z hz
    rw [levelEmb_lev a i c] at h
    have hco := Submission.Lib.K4XInterface.gobs_coarsen hN1 hr0 hrL
      (p.B k (a.γ (levelEmb a i c))) z
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    have : obs (p.B k (a.γ (levelEmb a i c))) (δ (p.N k) (r i)) z =
        Submission.Lib.K4XInterface.coarsenObs n
          (obs (p.B k (a.γ (levelEmb a i c))) (δ (p.N k) p.L) z) := hco
    rw [← this]
    exact h
  -- measurable decoders, one world at a time
  have hFm : ∀ c, MeasurableSet (a.F (levelEmb a i c)) := fun c =>
    (levelAtlas_charts hcore him (fun _ _ => ∅) c).2.2.2.2.2.2.2.1
  have hworld : ∀ γ : Fin (p.W k), ∃ Λ : Observation → Finset (Fin (levelSet a i).card),
      (∀ c, MeasurableSet {o | c ∈ Λ o}) ∧ (∀ o, ((Λ o).card : ℝ) ≤ a.κ) ∧
      ∀ c, a.γ (levelEmb a i c) = γ → ∀ z ∈ a.F (levelEmb a i c),
        c ∈ Λ (obs (p.B k γ) (δ (p.N k) p.L) z) := by
    intro γ
    obtain ⟨Λ, hm, hc, hs⟩ := measurable_decoder_of_source_images
      (fun c => if a.γ (levelEmb a i c) = γ then a.F (levelEmb a i c) else ∅)
      (fun c => by split_ifs; exacts [hFm c, MeasurableSet.empty])
      (obs (p.B k γ) (δ (p.N k) p.L)) (measurable_obs' _ _) a.κ (L γ) (hLcard γ)
      (fun c z hz => by
        by_cases h : a.γ (levelEmb a i c) = γ
        · rw [if_pos h] at hz
          have := hknown c z hz
          rw [h] at this
          exact this
        · rw [if_neg h] at hz; exact absurd hz (Set.notMem_empty _))
    refine ⟨Λ, hm, hc, fun c hγ z hz => hs c z ?_⟩
    rw [if_pos hγ]; exact hz
  choose Λ hΛm hΛc hΛs using hworld
  exact ⟨Λ, fun γ c => hΛm γ c, fun γ o => hΛc γ o,
    fun c z hz => hΛs (a.γ (levelEmb a i c)) c rfl z hz⟩

end

end Submission.Obl.k4_raw_localized_native_systems.C
