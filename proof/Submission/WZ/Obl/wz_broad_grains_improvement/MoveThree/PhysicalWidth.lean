-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PhysicalWidth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PhysicalWidth.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, PhysicalWidth.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CoarseCapCount
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainWitnesses
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainAxes
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd pd_triangle pd_symm pd_isometry)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis boxAxis_norm frozen_prism_ends coordinate_axis_close grain_axis_close)

/-- A whole grain inside a container has its long axis in the cap determined
by the container's middle width divided by the original grain length. -/
theorem contained_prism_axis_close {a b c A B ℓ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hA : 0 ≤ A) (hAB : A ≤ B)
    {z z' : V} (e g : V ≃ₗᵢ[ℝ] V)
    (hsub : P a b c z e ⊆ P A B ℓ z' g) :
    pd (boxAxis e 2) (boxAxis g 2) ≤ 3 * B / c := by
  obtain ⟨hplus, hminus⟩ := frozen_prism_ends ha hb hc.le z e
  have hB : 0 ≤ B := hA.trans hAB
  have hp := hsub hplus
  have hm := hsub hminus
  have hcoord (j : Fin 3) (d : ℝ)
      (hpj : |g (z + (c / 2) • boxAxis e 2 - z') j| ≤ d / 2)
      (hmj : |g (z - (c / 2) • boxAxis e 2 - z') j| ≤ d / 2) :
      |g (boxAxis e 2) j| ≤ d / c := by
    apply (le_div_iff₀ hc).mpr
    have he : g (z + (c / 2) • boxAxis e 2 - z') j -
        g (z - (c / 2) • boxAxis e 2 - z') j = c * g (boxAxis e 2) j := by
      rw [← PiLp.sub_apply, ← map_sub,
        show (z + (c / 2) • boxAxis e 2 - z') -
          (z - (c / 2) • boxAxis e 2 - z') = c • boxAxis e 2 by module,
        map_smul, PiLp.smul_apply, smul_eq_mul]
    have hh := (abs_sub _ _).trans (add_le_add hpj hmj)
    rw [he, abs_mul, abs_of_pos hc] at hh
    nlinarith only [hh]
  have h0 : |g (boxAxis e 2) 0| ≤ B / c :=
    (hcoord 0 A hp.1 hm.1).trans (div_le_div_of_nonneg_right hAB hc.le)
  have h1 := hcoord 1 B hp.2.1 hm.2.1
  have hh := coordinate_axis_close (show 0 ≤ B / c by positivity)
    (show ‖g (boxAxis e 2)‖ = 1 by rw [g.norm_map, boxAxis_norm]) h0 h1
  have he : pd (g (boxAxis e 2)) (EuclideanSpace.basisFun (Fin 3) ℝ 2) =
      pd (boxAxis e 2) (boxAxis g 2) := by
    conv_rhs => rw [← pd_isometry g]
    simp only [boxAxis, g.apply_symm_apply]
  rw [he] at hh
  simpa only [mul_div_assoc] using hh

/-- The physical width count uses only coarse essential distinctness and
disjointness within a coarse fibre. It is independent of the normalization
used to construct the containing prism. -/
theorem grain_container_overlap_count :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {ρ a b c A B ℓ : ℝ} {N L : ℕ}
      {y w : Fin N → V} {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
      {Hs : Fin L → Set V} {γ : Fin L → Fin N},
      0 < ρ → 0 ≤ a → 0 ≤ b → 0 < c → 0 ≤ A → A ≤ B →
      (∀ k, ‖w k‖ = 1) → X ρ N y w →
      (∀ j, Hs j ⊆ T ρ (y (γ j)) (w (γ j))) →
      (∀ j j', j ≠ j' → γ j = γ j' → Disjoint (Hs j) (Hs j')) →
      (∀ j, (e j (w (γ j)) 0) ^ 2 + (e j (w (γ j)) 1) ^ 2 ≤ (10 * ρ) ^ 2) →
      ∀ (Q : Finset (Fin L)) (z' : V) (g : V ≃ₗᵢ[ℝ] V),
        (∀ j ∈ Q, P a b c (z j) (e j) ⊆ P A B ℓ z' g) →
        ∀ p, q L {j | j ∈ Q ∧ p ∈ Hs j} ≤ C₀ * (1 + B / (ρ * c)) ^ 3 := by
  classical
  obtain ⟨C₀, hC₀, Hcount⟩ := coarse_projective_cap_count
  refine ⟨C₀ * 23 ^ 3, by positivity, ?_⟩
  intro ρ a b c A B ℓ N L y w z e Hs γ hρ ha hb hc hA hAB hw hX hHT hdisj
    halign Q z' g hsub p
  have hB : 0 ≤ B := hA.trans hAB
  let J := Q.filter (fun j => p ∈ Hs j)
  have hJ (j : Fin L) : j ∈ J ↔ j ∈ Q ∧ p ∈ Hs j := by simp [J]
  have hinj : Set.InjOn γ (↑J : Set (Fin L)) := by
    intro j hj k hk he
    by_contra hne
    exact Set.disjoint_left.mp (hdisj j k hne he) ((hJ j).mp hj).2 ((hJ k).mp hk).2
  have hcap (j : Fin L) (hj : j ∈ J) :
      pd (w (γ j)) (boxAxis g 2) ≤ 23 * (ρ + B / c) := by
    have h1 := grain_axis_close hρ.le (e j) (hw (γ j)) (halign j)
    rw [pd_symm] at h1
    have h2 := contained_prism_axis_close ha hb hc hA hAB (e j) g (hsub j ((hJ j).mp hj).1)
    rw [mul_div_assoc] at h2
    have h3 := pd_triangle (w (γ j)) (boxAxis (e j) 2) (boxAxis g 2)
    have hBc : 0 ≤ B / c := by positivity
    nlinarith
  have himage : (↑(J.image γ) : Set (Fin N)) ⊆
      {k | p ∈ T ρ (y k) (w k) ∧ pd (w k) (boxAxis g 2) ≤ 23 * (ρ + B / c)} := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨hHT j ((hJ j).mp hj).2, hcap j hj⟩
  have hcount := Hcount ρ (23 * (ρ + B / c)) hρ
    (by
      have : 0 ≤ B / c := by positivity
      linarith) N y w hw hX p (boxAxis g 2)
  change q N {k | p ∈ T ρ (y k) (w k) ∧
    pd (w k) (boxAxis g 2) ≤ 23 * (ρ + B / c)} ≤ _ at hcount
  calc
    q L {j | j ∈ Q ∧ p ∈ Hs j} = (J.card : ℝ) := by
      have he : {j | j ∈ Q ∧ p ∈ Hs j} = (↑J : Set (Fin L)) := by
        ext j
        simp [J]
      simp only [q, he, Set.ncard_coe_finset]
    _ = ((J.image γ).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ q N {k | p ∈ T ρ (y k) (w k) ∧
        pd (w k) (boxAxis g 2) ≤ 23 * (ρ + B / c)} := by
      dsimp only [q]
      exact_mod_cast Set.ncard_le_ncard himage (Set.toFinite _)
    _ ≤ C₀ * ((23 * (ρ + B / c)) / ρ) ^ 3 := hcount
    _ = (C₀ * 23 ^ 3) * (1 + B / (ρ * c)) ^ 3 := by
      field_simp

/-- High overlap of full old grains forces a middle-width increase in the
original coordinates. The sole scalar reserve is `q₀ > 3t`. -/
theorem physical_width_growth_of_overlap {C₀ δ ρ c B M q₀ t : ℝ}
    (hC₀ : 0 < C₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hc : 0 < c)
    (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hbudget : 8 * C₀ * δ ^ (q₀ - 3 * t) ≤ 1)
    (hcount : M ≤ C₀ * (1 + B / (ρ * c)) ^ 3) (hhigh : δ ^ (-q₀) < M) :
    δ ^ (-t) * ρ * c ≤ B := by
  by_contra hsmall
  have hsmall' : B / (ρ * c) < δ ^ (-t) := by
    apply (div_lt_iff₀ (mul_pos hρ hc)).mpr
    simpa only [mul_assoc] using lt_of_not_ge hsmall
  have hone : 1 ≤ δ ^ (-t) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hupper : M ≤ 8 * C₀ * δ ^ (-(3 * t)) := by
    calc
      M ≤ C₀ * (1 + B / (ρ * c)) ^ 3 := hcount
      _ ≤ C₀ * (2 * δ ^ (-t)) ^ 3 := by gcongr; linarith
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (δ ^ (-t)) 3, ← Real.rpow_mul hδ.le]
        norm_num
        rw [show t * 3 = 3 * t by ring]
        ring
  have hlast : 8 * C₀ * δ ^ (-(3 * t)) ≤ δ ^ (-q₀) := by
    calc
      _ = (8 * C₀ * δ ^ (q₀ - 3 * t)) * δ ^ (-q₀) := by
        conv_rhs => rw [mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ 1 * δ ^ (-q₀) := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = _ := one_mul _
  exact (hhigh.trans_le (hupper.trans hlast)).false

/-- A uniform power cutoff makes the overlap-to-width implication available
for arbitrary finite grain families and arbitrary physical containers. -/
theorem grain_container_width_growth {q₀ t : ℝ} (ht : 0 < t) (hq : 3 * t < q₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {ρ a b c A B ℓ : ℝ} {N L : ℕ}
        {y w : Fin N → V} {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs : Fin L → Set V} {γ : Fin L → Fin N},
      0 < ρ → 0 ≤ a → 0 ≤ b → 0 < c → 0 ≤ A → A ≤ B →
      (∀ k, ‖w k‖ = 1) → X ρ N y w →
      (∀ j, Hs j ⊆ T ρ (y (γ j)) (w (γ j))) →
      (∀ j j', j ≠ j' → γ j = γ j' → Disjoint (Hs j) (Hs j')) →
      (∀ j, (e j (w (γ j)) 0) ^ 2 + (e j (w (γ j)) 1) ^ 2 ≤ (10 * ρ) ^ 2) →
      ∀ (Q : Finset (Fin L)) (z' : V) (g : V ≃ₗᵢ[ℝ] V),
        (∀ j ∈ Q, P a b c (z j) (e j) ⊆ P A B ℓ z' g) →
        (∃ p, δ ^ (-q₀) < q L {j | j ∈ Q ∧ p ∈ Hs j}) →
        δ ^ (-t) * ρ * c ≤ B := by
  obtain ⟨C₀, hC₀, Hcount⟩ := grain_container_overlap_count
  let d₀ := min 1 ((1 / (8 * C₀)) ^ (1 / (q₀ - 3 * t)))
  have hd₀ : 0 < d₀ := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨d₀, hd₀, min_le_left _ _, ?_⟩
  intro δ hδ hδd ρ a b c A B ℓ N L y w z e Hs γ hρ ha hb hc hA hAB
    hw hX hHT hdisj halign Q z' g hsub hhigh
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hsmall : δ ^ (q₀ - 3 * t) ≤ 1 / (8 * C₀) := by
    calc
      _ ≤ ((1 / (8 * C₀)) ^ (1 / (q₀ - 3 * t))) ^ (q₀ - 3 * t) :=
        Real.rpow_le_rpow hδ.le (hδd.trans (min_le_right _ _)) (by linarith)
      _ = _ := by
        rw [← Real.rpow_mul (by positivity : 0 ≤ 1 / (8 * C₀)),
          one_div_mul_cancel (by linarith : q₀ - 3 * t ≠ 0), Real.rpow_one]
  obtain ⟨p, hp⟩ := hhigh
  exact physical_width_growth_of_overlap hC₀ hδ hδ1 hρ hc (hA.trans hAB) ht.le
    (by have hh := (le_div_iff₀ (by positivity : 0 < 8 * C₀)).mp hsmall; nlinarith)
    (Hcount hρ ha hb hc hA hAB hw hX hHT hdisj halign Q z' g hsub p) hp

/-- Specialization of physical width growth to the explicit frozen grain
witness. It also applies when `Q` is selected after an affine normalization. -/
theorem HB_container_width_growth {q₀ t : ℝ} (ht : 0 < t) (hq : 3 * t < q₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {h ρ a c b g m A B ℓ : ℝ} {n N L : ℕ}
        {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
        {y w : Fin N → V} {f : Fin n → Fin N}
        {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs : Fin L → Set V} {γ : Fin L → Fin N},
      0 < ρ → 0 ≤ A → A ≤ B → (∀ k, ‖w k‖ = 1) → X ρ N y w →
      GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m →
      ∀ (Q : Finset (Fin L)) (z' : V) (g' : V ≃ₗᵢ[ℝ] V),
        (∀ j ∈ Q, P a (ρ * c) c (z j) (e j) ⊆ P A B ℓ z' g') →
        (∃ p, δ ^ (-q₀) < q L {j | j ∈ Q ∧ p ∈ Hs j}) →
        δ ^ (-t) * ρ * c ≤ B := by
  obtain ⟨d₀, hd₀, hd₀1, H⟩ := grain_container_width_growth ht hq
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd h ρ a c b g m A B ℓ n N L x v S Z y w f z e Hs γ
    hρ hA hAB hw hX hHB Q z' g' hsub hhigh
  have ha : 0 < a := hδ.trans_le hHB.1
  have hb : 0 < ρ * c := ha.trans_le hHB.2.1
  have hc : 0 < c := hb.trans_le hHB.2.2.1
  exact H δ hδ hδd hρ ha.le hb.le hc hA hAB hw hX
    (fun j => (hHB.2.2.2.2.1 j).2.1.trans (hHB.2.2.2.2.1 j).2.2.1)
    hHB.2.2.2.2.2.1 (fun j => (hHB.2.2.2.2.1 j).2.2.2) Q z' g' hsub hhigh

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
