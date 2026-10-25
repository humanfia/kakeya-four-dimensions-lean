-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NonStickyBranch.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatExit
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.SBBranch
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.CellCount
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Profile
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Orientation
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CellProfile
-- Copied from session x0318 (o070 branch, commit 2c4a35f, file NonStickyBranch.lean), namespace renamed.

/-!
# The non-sticky branch of the aligned trichotomy

Files under `X305/` are copies of x0305's o038 helpers (o038 origin branch x0305), namespace
renamed to `WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
open Set MeasureTheory
open scoped ENNReal

open Classical in
/-- A fibre is KT-good when a `δ^ν` share of it is Katz–Tao with constant `K'`. -/
def KTGood {n : ℕ} (δ ν K' : ℝ) (x v : Fin n → Space) (F : Finset (Fin n)) : Prop :=
  ∃ F' ⊆ F, (F.card : ℝ) ≤ δ ^ (-ν) * F'.card ∧ ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal ((F'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card * δ ^ 2) ≤
      ENNReal.ofReal K' * volume W

open Classical in
/-- The per-fibre dichotomy at a fixed scale `δ`, as delivered by `fibre_dichotomy`. -/
def FibreDich (ν δ : ℝ) : Prop :=
  ∀ (n : ℕ) (x v : Fin n → Space), (∀ i, ‖v i‖ = 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) → Distinct (fun i => Tube δ (x i) (v i)) →
    ∀ (F : Finset (Fin n)), F.Nonempty → ∀ (K Λ : ℝ),
    (∀ (a b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space), δ ≤ a → a ≤ b → b ≤ Λ * a → b ≤ 2 →
      ((F.filter (fun i => Tube δ (x i) (v i) ⊆ e '' factorBox a b)).card : ℝ) * δ ^ 2 ≤
        K * a * b) →
    KTGood δ ν (K * δ ^ (-ν)) x v F ∨
    (∃ a b : ℝ, δ ≤ a ∧ Λ * a < b ∧ b ≤ 2 ∧
      LongFactor ν δ a b (fun j : Fin F.card =>
        Tube δ (x (F.equivFin.symm j)) (v (F.equivFin.symm j))))

lemma fibreDich_of_le (ν : ℝ) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d → FibreDich ν δ := by
  obtain ⟨d, hd, h⟩ := fibre_dichotomy ν hν
  exact ⟨d, hd, fun δ hδ h100 hδd n x v hv hb hs F hF K Λ hr => h δ hδ h100 hδd n x v hv hb hs F hF K Λ hr⟩

open Classical in
/-- KT-goodness transported along an injective re-indexing. -/
lemma KTGood.map {n m : ℕ} {δ ν K' : ℝ} {x v : Fin n → Space} (e : Fin m → Fin n)
    (he : Function.Injective e) {F : Finset (Fin m)}
    (h : KTGood δ ν K' (fun j => x (e j)) (fun j => v (e j)) F) :
    KTGood δ ν K' x v (F.map ⟨e, he⟩) := by
  obtain ⟨F', hF'F, hcard, hKT⟩ := h
  refine ⟨F'.map ⟨e, he⟩, Finset.map_subset_map.mpr hF'F, ?_, ?_⟩
  · simpa [Finset.card_map] using hcard
  · intro W hW
    have hc : ((F'.map ⟨e, he⟩).filter (fun i => Tube δ (x i) (v i) ⊆ W)).card =
        (F'.filter (fun j => Tube δ (x (e j)) (v (e j)) ⊆ W)).card := by
      rw [Finset.filter_map, Finset.card_map]
      rfl
    rw [hc]
    exact hKT W hW


open Classical in
/-- **Flat side of the non-sticky branch.** If the fibres of the parents that are not KT-good
carry half of the family, `flat_exit` on them gives frozen (C) on a `δ^θ/2` share. -/
theorem flat_side {δ ρ ν Λ ζ ζ₂ ζ₃ θ K KF : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν)
    (hζ : 0 ≤ ζ) (hζ₂ : 0 ≤ ζ₂) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hΛ : 16 * δ ^ (-ν - ζ₂ / 200) ≤ Λ) (h64 : 64 * δ ^ ν ≤ 1)
    (hdich : FibreDich ν δ) {n q : ℕ} (hn : 0 < n)
    (hpig : ∀ n' : ℕ, n' ≤ n → (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
        (Nat.log 2 ⌊(n' : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν))
    (herror : localFlatLoss * δ ^ (ζ₃ - ζ - 5 * (2 * ν)) ≤ 1)
    (hretain : 2 * δ ^ (θ - 2 * ν) ≤ 1)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (hKF0 : 0 ≤ KF) (hKF : 2 * KF ≤ δ ^ (-ζ))
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (KF * n) * volume W)
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hRsep : Distinct (fun l => Tube ρ (z l) (w l)))
    (par : Fin n → Fin q) (hpar : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (z (par i)) (w (par i)))
    (huniq : ∀ i l, Tube δ (x i) (v i) ⊆ Tube ρ (z l) (w l) → l = par i)
    (hround : ∀ l (a b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space), δ ≤ a → a ≤ b → b ≤ Λ * a → b ≤ 2 →
      (((Finset.univ.filter (fun i => par i = l)).filter
        (fun i => Tube δ (x i) (v i) ⊆ e '' factorBox a b)).card : ℝ) * δ ^ 2 ≤ K * a * b)
    (hmaj : n ≤ 2 * (Finset.univ.filter (fun i => ¬ KTGood δ ν (K * δ ^ (-ν)) x v
      (Finset.univ.filter (fun i' => par i' = par i)))).card) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ δ ^ θ * n ≤ 2 * k ∧
      FlatPrisms ζ₂ ζ₃ δ (fun i => Tube δ (x (g i)) (v (g i))) := by
  set fl : Fin n → Prop := fun i => ¬ KTGood δ ν (K * δ ^ (-ν)) x v
    (Finset.univ.filter (fun i' => par i' = par i)) with hfl
  set SF : Finset (Fin n) := Finset.univ.filter fl with hSF
  set nF := SF.card with hnFdef
  have hnF : 0 < nF := by omega
  let eF : Fin nF ≃ SF := SF.equivFin.symm
  let ι : Fin nF → Fin n := fun j => (eF j : Fin n)
  have hι : Function.Injective ι := fun a b h => eF.injective (Subtype.ext h)
  have hιSF : ∀ j, ι j ∈ SF := fun j => (eF j).2
  let xF : Fin nF → Space := fun j => x (ι j)
  let vF : Fin nF → Space := fun j => v (ι j)
  let parF : Fin nF → Fin q := fun j => par (ι j)
  have hnn : (n : ℝ) ≤ 2 * nF := by exact_mod_cast hmaj
  -- Frostman of the flat family
  have hFF : Frostman (δ ^ (-ζ)) (fun j => Tube δ (xF j) (vF j)) := by
    intro W hW
    have hc : ncard {j | Tube δ (xF j) (vF j) ⊆ W} ≤ ncard {i | Tube δ (x i) (v i) ⊆ W} :=
      ncard_le_ncard_of_injOn ι (fun j hj => hj) hι.injOn
    calc ENNReal.ofReal (ncard {j | Tube δ (xF j) (vF j) ⊆ W} : ℝ)
        ≤ ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) :=
          ENNReal.ofReal_le_ofReal (by exact_mod_cast hc)
      _ ≤ ENNReal.ofReal (KF * n) * volume W := hF W hW
      _ ≤ ENNReal.ofReal (δ ^ (-ζ) * nF) * volume W := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          calc KF * n ≤ KF * (2 * nF) := mul_le_mul_of_nonneg_left hnn hKF0
            _ = (2 * KF) * nF := by ring
            _ ≤ δ ^ (-ζ) * nF := mul_le_mul_of_nonneg_right hKF (Nat.cast_nonneg _)
  -- every fibre of the flat family is flat
  have hfibre_eq : ∀ j₀ : Fin nF, (Finset.univ.filter (fun j => parF j = parF j₀)).map ⟨ι, hι⟩ =
      Finset.univ.filter (fun i => par i = par (ι j₀)) := by
    intro j₀
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hi
      have hflj₀ : fl (ι j₀) := (Finset.mem_filter.mp (hιSF j₀)).2
      have hfli : fl i := by
        simp only [hfl] at hflj₀ ⊢
        rw [hi]; exact hflj₀
      have hiSF : i ∈ SF := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfli⟩
      refine ⟨eF.symm ⟨i, hiSF⟩, ?_, ?_⟩
      · simp only [parF, ι, Equiv.apply_symm_apply]; exact hi
      · simp only [ι, Equiv.apply_symm_apply]
  have hflat : ∀ l, (Finset.univ.filter (fun j => parF j = l)).Nonempty → ∃ a b : ℝ,
      δ ≤ a ∧ Λ * a < b ∧ b ≤ 2 ∧
      LongFactor ν δ a b (fun j : Fin (Finset.univ.filter (fun j => parF j = l)).card =>
        Tube δ (xF ((Finset.univ.filter (fun j => parF j = l)).equivFin.symm j))
          (vF ((Finset.univ.filter (fun j => parF j = l)).equivFin.symm j))) := by
    intro l hne
    have hround' : ∀ (a b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space), δ ≤ a → a ≤ b → b ≤ Λ * a →
        b ≤ 2 → (((Finset.univ.filter (fun j => parF j = l)).filter
          (fun j => Tube δ (xF j) (vF j) ⊆ e '' factorBox a b)).card : ℝ) * δ ^ 2 ≤
            K * a * b := by
      intro a b e h1 h2 h3 h4
      refine le_trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg δ)) (hround l a b e h1 h2 h3 h4)
      have : ((Finset.univ.filter (fun j => parF j = l)).filter
          (fun j => Tube δ (xF j) (vF j) ⊆ e '' factorBox a b)).card ≤
          ((Finset.univ.filter (fun i => par i = l)).filter
            (fun i => Tube δ (x i) (v i) ⊆ e '' factorBox a b)).card := by
        apply Finset.card_le_card_of_injOn ι
        · intro j hj
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            mem_ofPred_eq] at hj ⊢
          exact hj
        · exact hι.injOn
      exact_mod_cast this
    rcases hdich nF xF vF (fun j => hv _) (fun j => hball _)
      (fun i j hij => hsep _ _ (hι.ne hij)) _ hne K Λ hround' with hkt | hfl'
    · exfalso
      obtain ⟨j₀, hj₀⟩ := hne
      have hpl : parF j₀ = l := (Finset.mem_filter.mp hj₀).2
      have hflj₀ : fl (ι j₀) := (Finset.mem_filter.mp (hιSF j₀)).2
      apply hflj₀
      have hmap := KTGood.map ι hι hkt
      rw [← hpl, hfibre_eq j₀] at hmap
      exact hmap
    · exact hfl'
  obtain ⟨k, g, hg, hk, hC⟩ := flat_exit hδ hδ1 hν hζ hζ₂ hρ hρ8 hΛ h64 hnF
    (hpig nF (by
      have := Finset.card_le_univ SF
      simpa using this)) herror hretain xF vF (fun j => hv _) (fun j => hball _) hFF z w hw
    hRsep parF (fun j => hpar _) (fun j l h => huniq _ l h) hflat
  refine ⟨k, fun i => ι (g i), hι.comp hg, ?_, hC⟩
  have hθ0 : 0 ≤ δ ^ θ := by positivity
  calc δ ^ θ * n ≤ δ ^ θ * (2 * nF) := mul_le_mul_of_nonneg_left hnn hθ0
    _ = 2 * (δ ^ θ * nF) := by ring
    _ ≤ 2 * k := by linarith

open WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy (pop pop_pos pop_le pop_eq_of_whole)

/-- Remove the cells of population below `t`: whole cells go, the rest keep their populations,
and at most `t` elements per cell are lost. -/
lemma prune_small_cells {ι α : Type*} [DecidableEq ι] [DecidableEq α] (S : Finset ι)
    (κ : ι → α) (t : ℕ) :
    S.filter (fun i => t ≤ pop S κ i) ⊆ S ∧
    (∀ i ∈ S.filter (fun i => t ≤ pop S κ i), ∀ j ∈ S, κ j = κ i →
      j ∈ S.filter (fun i => t ≤ pop S κ i)) ∧
    (∀ i ∈ S.filter (fun i => t ≤ pop S κ i),
      pop (S.filter (fun i => t ≤ pop S κ i)) κ i = pop S κ i) ∧
    S.card ≤ (S.filter (fun i => t ≤ pop S κ i)).card + (S.image κ).card * t := by
  set S' := S.filter (fun i => t ≤ pop S κ i) with hS'
  have hpopeq : ∀ i j, κ j = κ i → pop S κ j = pop S κ i := by
    intro i j h
    unfold pop
    congr 1; ext k; simp [h]
  have hsub : S' ⊆ S := Finset.filter_subset _ _
  have hwhole : ∀ i ∈ S', ∀ j ∈ S, κ j = κ i → j ∈ S' := by
    intro i hi j hj hji
    rw [hS', Finset.mem_filter] at hi ⊢
    exact ⟨hj, by rw [hpopeq i j hji]; exact hi.2⟩
  refine ⟨hsub, hwhole, fun i hi => pop_eq_of_whole hsub κ hwhole hi, ?_⟩
  -- the removed elements lie in small cells, at most `t` per cell
  have hsplit : S.card = S'.card + (S.filter (fun i => ¬ t ≤ pop S κ i)).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have hsmall : (S.filter (fun i => ¬ t ≤ pop S κ i)).card ≤ (S.image κ).card * t := by
    have hcover : S.filter (fun i => ¬ t ≤ pop S κ i) ⊆ (S.image κ).biUnion
        (fun c => (S.filter (fun i => κ i = c)).filter (fun i => ¬ t ≤ pop S κ i)) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact Finset.mem_biUnion.mpr ⟨κ i, Finset.mem_image_of_mem κ hi.1,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hi.1, rfl⟩, hi.2⟩⟩
    refine (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans ?_)
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro c _
    by_cases hne : ((S.filter (fun i => κ i = c)).filter (fun i => ¬ t ≤ pop S κ i)).Nonempty
    · obtain ⟨i, hi⟩ := hne
      rw [Finset.mem_filter, Finset.mem_filter] at hi
      have hlt : pop S κ i < t := not_le.mp hi.2
      have : (S.filter (fun j => κ j = c)) = (S.filter (fun j => κ j = κ i)) := by
        rw [hi.1.2]
      calc ((S.filter (fun i => κ i = c)).filter (fun i => ¬ t ≤ pop S κ i)).card
          ≤ (S.filter (fun i => κ i = c)).card := Finset.card_filter_le _ _
        _ = pop S κ i := by rw [this]; rfl
        _ ≤ t := hlt.le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  omega


set_option maxHeartbeats 1000000 in
open Classical in
/-- **KT side of the non-sticky branch.** A share `S'` of an aligned prepared family on which
every `ρ`-cell is Katz–Tao with constant `K'` gives, after pruning small cells and re-balancing
the `τ`- and `ρ`-populations, x0305's frozen `SB` through `SB_of_KTcase`. -/
theorem kt_side {δ τ ρ ζ₁ ζ₂ ν K' KF : ℝ} (hδ : 0 < δ) (hν : 0 ≤ ν) (hδτ : 2 * δ ≤ τ)
    {m : ℕ} (hm : 2 ≤ m) (hρm : ρ = (m : ℝ) * τ) (hρ : ρ ≤ 1 / 10000)
    (hsc : τ ≤ δ ^ ζ₁ * ρ)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Sp) 1)
    (hcan : ∀ i, x i = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (hclsτ : ∀ i i', WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 τ (x i) (v i) = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 τ (x i') (v i'))
    (hclsρ : ∀ i i', WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 ρ (x i) (v i) = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.classKey 200000 ρ (x i') (v i'))
    (a b : ℕ)
    (hbalτ : ∀ i, 2 ^ a ≤ pop Finset.univ (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (τ / 20) (x i) (v i)) i ∧
      pop Finset.univ (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (τ / 20) (x i) (v i)) i < 2 ^ (a + 1))
    (hbalρ : ∀ i, 2 ^ b ≤ pop Finset.univ (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (x i) (v i)) i ∧
      pop Finset.univ (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (x i) (v i)) i < 2 ^ (b + 1))
    (S' : Finset (Fin n)) (hS'size : (n : ℝ) ≤ 2 * δ ^ (-ν) * S'.card)
    (hK'0 : 0 ≤ K')
    (hKT : ∀ i₀ ∈ S', ∀ W : Set WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Sp, Convex ℝ W →
      ENNReal.ofReal ((S'.filter (fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (x i) (v i) =
          WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (x i₀) (v i₀) ∧
          Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card * δ ^ 2) ≤
        ENNReal.ofReal K' * volume W)
    (hcτ : K' * τ ^ 2 ≤ δ ^ (-ζ₂) * (δ ^ (2 * ν) * 2 ^ a / 4) * δ ^ 2)
    (hfull : δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ (a + 4) ≤ δ ^ (3 * ν) * 2 ^ b)
    (hKF0 : 0 ≤ KF)
    (hFG : ∀ W : Set WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Sp, Convex ℝ W →
      ENNReal.ofReal ((Finset.univ.filter (fun i =>
        Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal (KF * n) * volume W)
    (hsmall : 16 * ((Nat.log 2 n : ℝ) + 1) * δ ^ ν ≤ 1)
    (hKF : 2 * (KF * (16 * ((Nat.log 2 n : ℝ) + 1) ^ 2 * δ ^ (-ν))) ≤ δ ^ (-ζ₂))
    (hζ₂ : 4 ≤ δ ^ (-ζ₂)) :
    ∃ S : Finset (Fin n), S.Nonempty ∧
      (n : ℝ) ≤ 16 * ((Nat.log 2 n : ℝ) + 1) ^ 2 * δ ^ (-ν) * S.card ∧
      WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.SBpred ζ₁ ζ₂ δ S.card (fun j => Metric.thickening δ
        (segment ℝ (x (S.equivFin.symm j).1) (x (S.equivFin.symm j).1 + v (S.equivFin.symm j).1))) := by
  set κτ : Fin n → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (τ / 20) (x i) (v i)
    with hκτ
  set κρ : Fin n → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell (ρ / 20) (x i) (v i)
    with hκρ
  have hτ0 : 0 < τ := by linarith
  have hnest : ∀ i j, κτ j = κτ i → κρ j = κρ i := by
    intro i j h
    have := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell_nest (by positivity : (0:ℝ) < τ / 20) (by omega : 0 < m) h
    simpa [hκρ, hρm, mul_div_assoc] using this
  have hδν : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ ν
  have hδνnν : δ ^ ν * δ ^ (-ν) = 1 := by rw [← Real.rpow_add hδ]; simp
  set Lg : ℝ := (Nat.log 2 n : ℝ) + 1 with hLg
  have hLg1 : 1 ≤ Lg := by have : (0:ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _; linarith
  -- number of cells
  have hcells : ∀ (κ : Fin n → (Fin 3 → ℤ) × (Fin 3 → ℤ)) (c : ℕ) (T : Finset (Fin n)),
      (∀ i, 2 ^ c ≤ pop Finset.univ κ i) → ((T.image κ).card : ℝ) * 2 ^ c ≤ n := by
    intro κ c T hpop
    have h1 : (T.image κ).card ≤ (Finset.univ.image κ).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.subset_univ _))
    have h2' : (Finset.univ.image κ).card * 2 ^ c ≤ (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_eq_sum_card_image κ (Finset.univ : Finset (Fin n)),
        ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro c' hc'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc'
      exact hpop i
    have h2 : (Finset.univ.image κ).card * 2 ^ c ≤ n := by
      simpa [Finset.card_univ, Fintype.card_fin] using h2'
    have : ((T.image κ).card : ℝ) * 2 ^ c ≤ ((Finset.univ.image κ).card : ℝ) * 2 ^ c :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (by positivity)
    exact this.trans (by exact_mod_cast h2)
  have hδν16 : δ ^ ν ≤ 1 / 16 := by
    have : 16 * δ ^ ν ≤ 16 * Lg * δ ^ ν := by nlinarith
    linarith
  have hlog_le : ∀ T : Finset (Fin n), ((Nat.log 2 T.card : ℝ) + 1) ≤ Lg := by
    intro T
    have hT : T.card ≤ n := by simpa using Finset.card_le_univ T
    have : Nat.log 2 T.card ≤ Nat.log 2 n := Nat.log_mono_right hT
    rw [hLg]; exact_mod_cast Nat.add_le_add_right this 1
  -- max (1, ⌊X⌋₊) ≥ X / 2
  have hfloor_half : ∀ X : ℝ, 0 ≤ X → ∀ p : ℕ, 1 ≤ p → ⌊X⌋₊ ≤ p → X / 2 ≤ p := by
    intro X hX p hp hpX
    by_cases h2 : X ≤ 2
    · have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    · have h1 : X < ⌊X⌋₊ + 1 := Nat.lt_floor_add_one X
      have h3 : (⌊X⌋₊ : ℝ) ≤ p := by exact_mod_cast hpX
      push Not at h2
      linarith
  -- step 1: prune small τ-cells of S'
  set t0 : ℕ := ⌊δ ^ (2 * ν) * 2 ^ a⌋₊ with ht0
  obtain ⟨hS₀sub, hS₀whole, hS₀pop, hS₀card⟩ := prune_small_cells S' κτ t0
  set S₀ := S'.filter (fun i => t0 ≤ pop S' κτ i) with hS₀
  have hloss0 : (((S'.image κτ).card * t0 : ℕ) : ℝ) ≤ δ ^ (2 * ν) * n := by
    have hc := hcells κτ a S' (fun i => (hbalτ i).1)
    have ht0le : (t0 : ℝ) ≤ δ ^ (2 * ν) * 2 ^ a := Nat.floor_le (by positivity)
    push_cast
    calc ((S'.image κτ).card : ℝ) * t0 ≤ (S'.image κτ).card * (δ ^ (2 * ν) * 2 ^ a) :=
          mul_le_mul_of_nonneg_left ht0le (Nat.cast_nonneg _)
      _ = δ ^ (2 * ν) * ((S'.image κτ).card * 2 ^ a) := by ring
      _ ≤ δ ^ (2 * ν) * n := mul_le_mul_of_nonneg_left hc (by positivity)
  have e2 : δ ^ (2 * ν) = δ ^ ν * δ ^ ν := by rw [← Real.rpow_add hδ]; ring_nf
  have e3 : δ ^ (3 * ν) = δ ^ ν * δ ^ ν * δ ^ ν := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
  have hS'size' : (n : ℝ) * δ ^ ν / 2 ≤ S'.card := by
    have := mul_le_mul_of_nonneg_left hS'size hδν.le
    have h' : δ ^ ν * (2 * δ ^ (-ν) * S'.card) = 2 * S'.card := by
      rw [show δ ^ ν * (2 * δ ^ (-ν) * S'.card) = 2 * (δ ^ ν * δ ^ (-ν)) * S'.card by ring,
        hδνnν, mul_one]
    rw [h'] at this
    linarith
  have hS₀size : (n : ℝ) * δ ^ ν / 4 ≤ S₀.card := by
    have h1 : (S'.card : ℝ) ≤ S₀.card + δ ^ (2 * ν) * n := by
      have : (S'.card : ℝ) ≤ (S₀.card : ℝ) + (((S'.image κτ).card * t0 : ℕ) : ℝ) := by
        exact_mod_cast hS₀card
      linarith
    have h2 : δ ^ (2 * ν) * n ≤ (n : ℝ) * δ ^ ν / 4 := by
      rw [e2]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS₀ne : S₀.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S₀.card := lt_of_lt_of_le (by positivity) hS₀size
    exact_mod_cast this
  -- step 2: one dyadic class of τ-populations
  obtain ⟨S₁, hS₁sub, hS₁ne, hS₁card, hS₁whole, a', ha'⟩ :=
    WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.dyadic_class_refine S₀ hS₀ne κτ
  have hS₁size : (n : ℝ) * δ ^ ν / (4 * Lg) ≤ S₁.card := by
    have h := hS₁card
    have hl := hlog_le S₀
    have hpos : 0 < Lg := by linarith
    rw [div_le_iff₀ (by positivity)]
    calc (n : ℝ) * δ ^ ν = 4 * ((n : ℝ) * δ ^ ν / 4) := by ring
      _ ≤ 4 * S₀.card := by linarith
      _ ≤ 4 * (((Nat.log 2 S₀.card : ℝ) + 1) * S₁.card) := by linarith
      _ ≤ 4 * (Lg * S₁.card) := by
          have : 0 ≤ (S₁.card : ℝ) := Nat.cast_nonneg _
          nlinarith
      _ = S₁.card * (4 * Lg) := by ring
  -- step 3: prune small ρ-cells of S₁
  set t1 : ℕ := ⌊δ ^ (3 * ν) * 2 ^ b⌋₊ with ht1
  obtain ⟨hS₂sub, hS₂whole, hS₂pop, hS₂card⟩ := prune_small_cells S₁ κρ t1
  set S₂ := S₁.filter (fun i => t1 ≤ pop S₁ κρ i) with hS₂
  have hloss1 : (((S₁.image κρ).card * t1 : ℕ) : ℝ) ≤ δ ^ (3 * ν) * n := by
    have hc := hcells κρ b S₁ (fun i => (hbalρ i).1)
    have ht1le : (t1 : ℝ) ≤ δ ^ (3 * ν) * 2 ^ b := Nat.floor_le (by positivity)
    push_cast
    calc ((S₁.image κρ).card : ℝ) * t1 ≤ (S₁.image κρ).card * (δ ^ (3 * ν) * 2 ^ b) :=
          mul_le_mul_of_nonneg_left ht1le (Nat.cast_nonneg _)
      _ = δ ^ (3 * ν) * ((S₁.image κρ).card * 2 ^ b) := by ring
      _ ≤ δ ^ (3 * ν) * n := mul_le_mul_of_nonneg_left hc (by positivity)
  have hS₂size : (n : ℝ) * δ ^ ν / (8 * Lg) ≤ S₂.card := by
    have h1 : (S₁.card : ℝ) ≤ S₂.card + δ ^ (3 * ν) * n := by
      have : (S₁.card : ℝ) ≤ (S₂.card : ℝ) + (((S₁.image κρ).card * t1 : ℕ) : ℝ) := by
        exact_mod_cast hS₂card
      linarith
    have hpos : 0 < Lg := by linarith
    have h2 : δ ^ (3 * ν) * n ≤ (n : ℝ) * δ ^ ν / (8 * Lg) := by
      rw [e3, le_div_iff₀ (by positivity)]
      have hsm : 16 * Lg * δ ^ ν ≤ 1 := hsmall
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hd0 : 0 ≤ δ ^ ν := hδν.le
      have hLd : 0 ≤ Lg * δ ^ ν := mul_nonneg (by linarith) hd0
      have h8 : 8 * Lg * δ ^ ν ≤ 1 := by linarith
      have hd1 : δ ^ ν ≤ 1 := by linarith
      calc δ ^ ν * δ ^ ν * δ ^ ν * n * (8 * Lg)
          = (δ ^ ν * n) * (δ ^ ν * (8 * Lg * δ ^ ν)) := by ring
        _ ≤ (δ ^ ν * n) * (δ ^ ν * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8 hd0) (mul_nonneg hd0 hn0)
        _ ≤ (δ ^ ν * n) * 1 := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left hd1 (mul_nonneg hd0 hn0)
        _ = n * δ ^ ν := by ring
    have : (n : ℝ) * δ ^ ν / (8 * Lg) = (n : ℝ) * δ ^ ν / (4 * Lg) / 2 := by
      field_simp; ring
    linarith
  have hS₂ne : S₂.Nonempty := by
    rw [← Finset.card_pos]
    have hpos : 0 < Lg := by linarith
    have : (0 : ℝ) < S₂.card := lt_of_lt_of_le (by positivity) hS₂size
    exact_mod_cast this
  -- step 4: one dyadic class of ρ-populations
  obtain ⟨S₃, hS₃sub, hS₃ne, hS₃card, hS₃whole, b', hb'⟩ :=
    WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.dyadic_class_refine S₂ hS₂ne κρ
  have hS₃size : (n : ℝ) ≤ 16 * Lg ^ 2 * δ ^ (-ν) * S₃.card := by
    have hpos : 0 < Lg := by linarith
    have hl := hlog_le S₂
    have h1 : (n : ℝ) * δ ^ ν / (8 * Lg) ≤ Lg * S₃.card := by
      have : (S₂.card : ℝ) ≤ Lg * S₃.card := by
        have : 0 ≤ (S₃.card : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    have h2 : (n : ℝ) * δ ^ ν ≤ 8 * Lg ^ 2 * S₃.card := by
      rw [div_le_iff₀ (by positivity)] at h1; nlinarith
    have h3 : (n : ℝ) = δ ^ (-ν) * ((n : ℝ) * δ ^ ν) := by
      rw [mul_comm (n : ℝ), ← mul_assoc, mul_comm (δ ^ (-ν)), hδνnν, one_mul]
    have hnν : 0 ≤ δ ^ (-ν) := Real.rpow_nonneg hδ.le _
    have hq : 0 ≤ Lg ^ 2 * δ ^ (-ν) * S₃.card :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hnν) (Nat.cast_nonneg _)
    calc (n : ℝ) = δ ^ (-ν) * ((n : ℝ) * δ ^ ν) := h3
      _ ≤ δ ^ (-ν) * (8 * Lg ^ 2 * S₃.card) := mul_le_mul_of_nonneg_left h2 hnν
      _ = 8 * (Lg ^ 2 * δ ^ (-ν) * S₃.card) := by ring
      _ ≤ 16 * (Lg ^ 2 * δ ^ (-ν) * S₃.card) := by linarith
      _ = 16 * Lg ^ 2 * δ ^ (-ν) * S₃.card := by ring
  -- populations along the chain S₃ ⊆ S₂ ⊆ S₁ ⊆ S₀ ⊆ S'
  have hS₃sub₁ : S₃ ⊆ S₁ := hS₃sub.trans hS₂sub
  have hS₃wholeτ : ∀ i ∈ S₃, ∀ j ∈ S₁, κτ j = κτ i → j ∈ S₃ := by
    intro i hi j hj hji
    have hρji : κρ j = κρ i := hnest i j hji
    have hj₂ : j ∈ S₂ := hS₂whole i (hS₃sub hi) j hj hρji
    exact hS₃whole i hi j hj₂ hρji
  have hpopτ : ∀ i ∈ S₃, pop S₃ κτ i = pop S' κτ i := by
    intro i hi
    rw [pop_eq_of_whole hS₃sub₁ κτ hS₃wholeτ hi,
      pop_eq_of_whole hS₁sub κτ hS₁whole (hS₃sub₁ hi), hS₀pop i (hS₁sub (hS₃sub₁ hi))]
  have hpopρ : ∀ i ∈ S₃, pop S₃ κρ i = pop S₁ κρ i := by
    intro i hi
    rw [pop_eq_of_whole hS₃sub κρ hS₃whole hi, hS₂pop i (hS₃sub hi)]
  obtain ⟨i₀, hi₀⟩ := hS₃ne
  have hi₀S₁ : i₀ ∈ S₁ := hS₃sub₁ hi₀
  have hi₀S₀ : i₀ ∈ S₀ := hS₁sub hi₀S₁
  have hi₀S' : i₀ ∈ S' := hS₀sub hi₀S₀
  -- the τ class
  have ha'low : δ ^ (2 * ν) * 2 ^ a / 4 ≤ (2 : ℝ) ^ a' := by
    have hp := (ha' i₀ hi₀S₁).2
    have ht : t0 ≤ pop S' κτ i₀ := (Finset.mem_filter.mp hi₀S₀).2
    have h1 : 1 ≤ pop S' κτ i₀ := pop_pos hi₀S'
    have hhalf := hfloor_half (δ ^ (2 * ν) * 2 ^ a) (by positivity) _ h1 ht
    have heq : pop S₁ κτ i₀ = pop S' κτ i₀ := by
      rw [pop_eq_of_whole hS₁sub κτ hS₁whole hi₀S₁, hS₀pop i₀ hi₀S₀]
    have hpR : (pop S' κτ i₀ : ℝ) < 2 ^ (a' + 1) := by rw [← heq]; exact_mod_cast hp
    rw [pow_succ] at hpR
    linarith
  have ha'up : (2 : ℝ) ^ a' < 2 ^ (a + 1) := by
    have hp := (ha' i₀ hi₀S₁).1
    have heq : pop S₁ κτ i₀ = pop S' κτ i₀ := by
      rw [pop_eq_of_whole hS₁sub κτ hS₁whole hi₀S₁, hS₀pop i₀ hi₀S₀]
    have hle : pop S' κτ i₀ ≤ pop Finset.univ κτ i₀ :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    have h2 := (hbalτ i₀).2
    have : 2 ^ a' < 2 ^ (a + 1) := by
      calc 2 ^ a' ≤ pop S₁ κτ i₀ := hp
        _ = pop S' κτ i₀ := heq
        _ ≤ pop Finset.univ κτ i₀ := hle
        _ < 2 ^ (a + 1) := h2
    exact_mod_cast this
  -- the ρ class
  have hb'low : δ ^ (3 * ν) * 2 ^ b / 4 ≤ (2 : ℝ) ^ b' := by
    have hp := (hb' i₀ hi₀).2
    have hi₀S₂ : i₀ ∈ S₂ := hS₃sub hi₀
    have ht : t1 ≤ pop S₁ κρ i₀ := (Finset.mem_filter.mp hi₀S₂).2
    have h1 : 1 ≤ pop S₁ κρ i₀ := pop_pos hi₀S₁
    have hhalf := hfloor_half (δ ^ (3 * ν) * 2 ^ b) (by positivity) _ h1 ht
    have hpR : (pop S₁ κρ i₀ : ℝ) < 2 ^ (b' + 1) := by rw [← hpopρ i₀ hi₀]; exact_mod_cast hp
    rw [pow_succ] at hpR
    linarith
  have hτ2 : 0 < δ ^ (-ζ₂) * δ ^ 2 := by positivity
  set KF' : ℝ := KF * (16 * Lg ^ 2 * δ ^ (-ν)) with hKF'def
  refine ⟨S₃, ⟨i₀, hi₀⟩, hS₃size, ?_⟩
  refine WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.SB_of_KTcase hδ hδτ hm hρm hρ hsc x v hv hT hcan hanti S₃ ⟨i₀, hi₀⟩
    (fun i _ i' _ => hclsτ i i') (fun i _ i' _ => hclsρ i i') a' b' ?_ ?_ hK'0 ?_ ?_ ?_
    (by positivity) ?_ hKF hζ₂
  · intro i hi
    have h := ha' i (hS₃sub₁ hi)
    rw [pop_eq_of_whole hS₃sub₁ κτ hS₃wholeτ hi]
    exact h
  · intro i hi; exact hb' i hi
  · intro i hi W hW
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hKT i (hS₀sub (hS₁sub (hS₃sub₁ hi))) W hW)
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg δ)
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset_filter _ (hS₀sub.trans' (hS₁sub.trans' hS₃sub₁)))
  · calc K' * τ ^ 2 ≤ δ ^ (-ζ₂) * (δ ^ (2 * ν) * 2 ^ a / 4) * δ ^ 2 := hcτ
      _ ≤ δ ^ (-ζ₂) * 2 ^ a' * δ ^ 2 := by
          have := mul_le_mul_of_nonneg_left ha'low (Real.rpow_nonneg hδ.le (-ζ₂))
          nlinarith
  · have hr : 0 ≤ δ ^ ζ₂ * (ρ / τ) ^ 2 := by positivity
    calc δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ (a' + 1) = 2 * (δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ a') := by
          rw [pow_succ]; ring
      _ ≤ 2 * (δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ (a + 1)) := by
          have := mul_le_mul_of_nonneg_left ha'up.le hr
          linarith
      _ = (δ ^ ζ₂ * (ρ / τ) ^ 2 * 2 ^ (a + 4)) / 4 := by ring
      _ ≤ (δ ^ (3 * ν) * 2 ^ b) / 4 := by linarith
      _ ≤ 2 ^ b' := hb'low
  · intro W hW
    have hc : (S₃.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card ≤
        (Finset.univ.filter (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    refine le_trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast hc)) ((hFG W hW).trans ?_)
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    calc KF * n ≤ KF * (16 * Lg ^ 2 * δ ^ (-ν) * S₃.card) :=
          mul_le_mul_of_nonneg_left hS₃size hKF0
      _ = KF' * S₃.card := by rw [hKF'def]; ring

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
