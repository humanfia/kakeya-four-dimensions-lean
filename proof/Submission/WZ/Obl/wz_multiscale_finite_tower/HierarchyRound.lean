-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyRound.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.RefineBadGaps

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

theorem refine_hierarchy_round {σ ω : ℝ} (hE : Endpoint σ ω) (hOne : OneScale σ ω)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (B : ℕ) {g g' gap gap' ε D : ℝ} (hg' : 0 < g') (hgg : g' ≤ g)
    (hmesh : (1 - ω / 100) * g < g') (hgap : gap' ≤ gap)
    (hgap' : 0 < gap') (hgap'' : gap' < ω / 100 * g') (hε : 0 < ε) (hD : 0 < D) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ D ∧ d₀ ≤ 1 / 100000 ∧
      ∀ d θ : ℝ, ∀ J : ℕ, 0 < d → d ≤ d₀ → 0 ≤ θ → θ ≤ η → J ≤ B →
      ∀ C : HierarchyCertificate d θ g gap J,
      VolumeBound σ ω κ α d (C.tree.layer J).card C.shading ∨
        RetainedHierarchy d ε g' gap' (2 * B) (C.tree.layer J).card C.shading := by
  obtain ⟨α, κ, η, d₀, hα, hκ, hη, hd₀, hd₀D, hd₀small, HI⟩ :=
    refine_bad_gaps hE hOne hσ hσ1 hω hω1 (2 * B) B hg' hgg hmesh hgap' hgap'' hε hD
  refine ⟨α, κ, η, d₀, hα, hκ, hη, hd₀, hd₀D, hd₀small, ?_⟩
  intro d θ J hd hdd hθ hθη hJB C
  have hd1 : d ≤ 1 := by have hh := hdd.trans hd₀small; linarith
  let C' := C.weaken_gap hd hd1 hgap
  have hbad := badGaps_card_le d g' J (fun j => (C'.tree.layer j).radius)
  exact HI d θ J hd hdd hθ hθη C' (hbad.trans hJB) (by omega)

noncomputable def depthMesh (ω β : ℝ) (q : ℕ) : ℝ := (1 - ω / 100) ^ q + β

noncomputable def depthGap (ω β : ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | q + 1 => min (depthGap ω β q) (ω / 100 * depthMesh ω β (q + 1) / 2)

lemma depthMesh_pos {ω β : ℝ} (hω : ω ≤ 1) (hβ : 0 < β) (q : ℕ) : 0 < depthMesh ω β q := by
  have ha : 0 ≤ 1 - ω / 100 := by linarith
  have hh := pow_nonneg ha q
  dsimp [depthMesh]
  linarith

lemma depthMesh_succ_le {ω β : ℝ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (q : ℕ) :
    depthMesh ω β (q + 1) ≤ depthMesh ω β q := by
  dsimp [depthMesh]
  rw [pow_succ]
  have hpow := pow_nonneg (show 0 ≤ 1 - ω / 100 by linarith) q
  nlinarith

lemma depthMesh_slack {ω β : ℝ} (hω : 0 < ω) (hβ : 0 < β) (q : ℕ) :
    (1 - ω / 100) * depthMesh ω β q < depthMesh ω β (q + 1) := by
  dsimp [depthMesh]
  rw [pow_succ]
  nlinarith only [mul_pos hω hβ]

lemma depthGap_pos {ω β : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) (hβ : 0 < β) (q : ℕ) :
    0 < depthGap ω β q := by
  induction q with
  | zero => norm_num [depthGap]
  | succ q ih =>
    exact lt_min ih (by have hh := depthMesh_pos hω1 hβ (q + 1); positivity)

lemma depthGap_succ_le (ω β : ℝ) (q : ℕ) : depthGap ω β (q + 1) ≤ depthGap ω β q := min_le_left _ _

lemma depthGap_succ_lt {ω β : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) (hβ : 0 < β) (q : ℕ) :
    depthGap ω β (q + 1) < ω / 100 * depthMesh ω β (q + 1) := by
  have hh : 0 < ω / 100 * depthMesh ω β (q + 1) := mul_pos (by positivity) (depthMesh_pos hω1 hβ _)
  exact (min_le_right _ _).trans_lt (by linarith)

end WangZahlLot.Obl.wz_multiscale_finite_tower
