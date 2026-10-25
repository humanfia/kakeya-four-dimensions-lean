-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Frostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.PowerCounts
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Packing

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

noncomputable def ballCount (S : Finset Plane) (x : Plane) (r : ℝ) : ℕ := by
  classical
  exact (S.filter (fun y => y ∈ Metric.ball x r)).card

/-- The counting form of the normalized one-dimensional Frostman condition. -/
def FiniteFrostman (δ C : ℝ) (S : Finset Plane) : Prop :=
  ∀ (x : Plane) (r : ℝ), δ ≤ r → (ballCount S x r : ℝ) ≤ C * r * (S.card : ℝ)

def FrostmanNet (δ C N : ℝ) (F : Set Plane) (S : Finset Plane) : Prop :=
  (↑S : Set Plane) ⊆ F ∧ N ≤ (S.card : ℝ) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ < dist a b) ∧
    (∀ x ∈ F, ∃ a ∈ S, dist x a ≤ δ) ∧ FiniteFrostman δ C S

theorem AD.separated_card_bound {δ C : ℝ} {F : Set Plane} (h : AD δ C F)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hF : InUnitSquare F)
    (S : Finset Plane) (hSF : (↑S : Set Plane) ⊆ F)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ dist a b) :
    (S.card : ℝ) ≤ 75 * C / δ := by
  obtain ⟨m, c, hc, hm⟩ := h.exists_global_cover hF (by linarith)
  have hs := separated_card_le_twentyfive_mul_cover hδ S hsep (hc.mono_set hSF)
  have hs' : (S.card : ℝ) ≤ 25 * (m : ℝ) := by exact_mod_cast hs
  calc (S.card : ℝ) ≤ 25 * (m : ℝ) := hs'
    _ ≤ 25 * (C * (3 / δ)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = 75 * C / δ := by ring

theorem AD.separated_ballCount {δ C : ℝ} {F : Set Plane} (h : AD δ C F)
    (hδ : 0 < δ) (S : Finset Plane) (hSF : (↑S : Set Plane) ⊆ F)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ dist a b)
    (x : Plane) (r : ℝ) (hδr : δ ≤ r) :
    (ballCount S x r : ℝ) ≤ 25 * C * (r / δ) := by
  classical
  obtain ⟨m, c, hc, hm⟩ := h x δ r le_rfl hδr
  let T := S.filter (fun a => a ∈ Metric.ball x r)
  have hTsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → δ ≤ dist a b := by
    intro a ha b hb hab
    exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  have hTcov : Covers δ (↑T : Set Plane) c := by
    apply hc.mono_set
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact ⟨hSF ha'.1, ha'.2⟩
  have hcard := separated_card_le_twentyfive_mul_cover hδ T hTsep hTcov
  have hc' : (ballCount S x r : ℝ) ≤ 25 * (m : ℝ) := by exact_mod_cast hcard
  nlinarith

/-- A separated internal net inherits the AD bound as a normalized counting
Frostman bound. The loss is explicit and absolute. -/
theorem AD.exists_frostman_net {δ C N : ℝ} {F : Set Plane} (h : AD δ C F)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hN : 0 < N) (hF : Bornology.IsBounded F)
    (hcover : CoverLower δ F N) :
    ∃ S : Finset Plane, FrostmanNet δ (25 * C / (δ * N)) N F S := by
  classical
  obtain ⟨m, c, hNm, hcF, hcsep, hcov⟩ :=
    hcover.exists_separated (hF.isCompact_closure.totallyBounded.subset subset_closure) hδ
  let S : Finset Plane := Finset.univ.image c
  have hci : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hd := hcsep i j hne
    rw [hij, dist_self] at hd
    exact (not_lt_of_ge hδ.le) hd
  have hScard : S.card = m := by
    simp only [S, Finset.card_image_of_injective _ hci, Finset.card_fin]
  have hNS : N ≤ (S.card : ℝ) := by simpa [hScard] using hNm
  have hSF : (↑S : Set Plane) ⊆ F := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hcF i
  have hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ < dist a b := by
    intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact hcsep i j (fun hij => hab (congrArg c hij))
  refine ⟨S, hSF, hNS, hsep, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact ⟨c i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩
  · intro x r hδr
    have hcount := h.separated_ballCount hδ S hSF
      (fun a ha b hb hab => (hsep a ha b hb hab).le) x r hδr
    calc (ballCount S x r : ℝ) ≤ 25 * C * (r / δ) := hcount
      _ = (25 * C / (δ * N)) * r * N := by field_simp
      _ ≤ (25 * C / (δ * N)) * r * (S.card : ℝ) := by
        apply mul_le_mul_of_nonneg_left hNS
        exact mul_nonneg (by positivity) (hδ.le.trans hδr)

/-- The large-triple hypothesis supplies large separated nets in both factors,
with the explicit normalized Frostman constant `225 * δ^(-4η)`. -/
theorem exists_frostman_nets_of_large_triples {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {F G : Set Plane} (hF : InUnitSquare F) (hG : InUnitSquare G)
    (hAF : AD δ (δ ^ (-η)) F) (hAG : AD δ (δ ^ (-η)) G)
    {Q : Set Triple} (hQ : Q ⊆ F ×ˢ (G ×ˢ G))
    (hN : CoverLower δ Q (δ ^ (η - 3))) :
    ∃ S T : Finset Plane,
      FrostmanNet δ (225 * δ ^ (-4 * η)) (δ ^ (3 * η - 1) / 9) F S ∧
      FrostmanNet δ (225 * δ ^ (-4 * η)) (δ ^ (3 * η - 1) / 9) G T := by
  obtain ⟨hFc, hGc⟩ := factor_coverLower_rpow hδ hδ1 hF hG hAF hAG hQ hN
  obtain ⟨S, hS⟩ := hAF.exists_frostman_net hδ (by positivity) (by positivity)
    hF.isBounded hFc
  obtain ⟨T, hT⟩ := hAG.exists_frostman_net hδ (by positivity) (by positivity)
    hG.isBounded hGc
  exact ⟨S, T, by simpa only [frostman_constant_eq hδ] using And.intro hS hT⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
