-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Basic

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open MeasureTheory Set

noncomputable section

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Tube := WangZahlLot.Obl.wz_tower_balanced_refinement.Tube
abbrev Admissible := WangZahlLot.Obl.wz_tower_balanced_refinement.Admissible

abbrev FiberCount (s L : ℝ) (n : ℕ) (P : Fin n → Prop) (U : Fin n → Set Space) : Prop :=
  ∀ W, Convex ℝ W →
    ENNReal.ofReal ((Set.ncard {i | P i ∧ U i ⊆ W} : ℝ) * s ^ 2) ≤
      ENNReal.ofReal L * volume W

abbrev FiberSlab (r : ℝ) (y w : Space) (L : ℝ) (n : ℕ)
    (P : Fin n → Prop) (U : Fin n → Set Space) : Prop :=
  ∀ (u : Space) (t ρ : ℝ), ‖u‖ = 1 → 0 < ρ →
    ENNReal.ofReal (Set.ncard {i | P i ∧ U i ⊆
      Tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w) ∩
        {p | |inner ℝ u p - t| ≤ ρ}} : ℝ) *
      volume (Tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w)) ≤
    ENNReal.ofReal (L * Set.ncard {i | P i}) *
      volume (Tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w) ∩
        {p | |inner ℝ u p - t| ≤ ρ})

abbrev StrongTower (d L g : ℝ) (B n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ J : ℕ, 1 ≤ J ∧ J ≤ B ∧ ∃ (r : ℕ → ℝ) (N : ℕ → ℕ)
    (y w : ∀ j, Fin (N j) → Space) (f : ∀ j, Fin (N (j + 1)) → Fin (N j)),
    r 0 = 1 ∧ r J = d ∧ N 0 = 1 ∧
    (∃ u : Fin n ≃ Fin (N J), ∀ i, y J (u i) = x i ∧ w J (u i) = v i) ∧
    (∀ j, j ≤ J → ∀ k, ‖w j k‖ = 1) ∧
    (∀ j, j < J → 0 < r (j + 1) ∧ r (j + 1) < r j ∧ d ^ g * r j ≤ r (j + 1) ∧
      ∀ i, Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i) ⊆
        Tube (r j) (y j (f j i)) (w j (f j i))) ∧
    ∀ j, j < J → ∀ k,
      FiberCount (r (j + 1)) L (N (j + 1)) (fun i => f j i = k)
        (fun i => Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i)) ∧
      FiberSlab (r j) (y j k) (w j k) L (N (j + 1)) (fun i => f j i = k)
        (fun i => Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i))

abbrev Gap (ω : ℝ) (q : ℕ) : ℝ := (2 - (1 / 2 : ℝ) ^ q) * (1 - ω / 100) ^ q

abbrev Depth (σ ω : ℝ) (q : ℕ) : Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D →
    ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y,
      Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        volume (⋃ i, Y i) ∨
      (δ ≤ D ∧ ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M L : ℝ),
        Admissible δ ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
        ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
        StrongTower δ (δ ^ (-ε)) (Gap ω q) (2 ^ q) m x' v')

abbrev Fiber (r s η : ℝ) (y w : Space) (n : ℕ)
    (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ Tube s (x i) (v i) ⊆ Tube r y w ∧
    MeasurableSet (Y i) ∧ Y i ⊆ Tube s (x i) (v i)) ∧
  ENNReal.ofReal ((s / r) ^ η * n * s ^ 2) ≤ ∑ i, volume (Y i) ∧
  FiberCount s ((s / r) ^ (-η)) n (fun _ => True) (fun i => Tube s (x i) (v i)) ∧
  FiberSlab r y w ((s / r) ^ (-η)) n (fun _ => True) (fun i => Tube s (x i) (v i))

lemma fiberCount_mono {s L L' : ℝ} {n : ℕ} {P : Fin n → Prop} {U : Fin n → Set Space}
    (h : FiberCount s L n P U) (hL : L ≤ L') : FiberCount s L' n P U := by
  intro W hW
  exact (h W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl)

lemma fiberSlab_mono {r L L' : ℝ} {y w : Space} {n : ℕ}
    {P : Fin n → Prop} {U : Fin n → Set Space}
    (h : FiberSlab r y w L n P U) (hL : L ≤ L') : FiberSlab r y w L' n P U := by
  intro u t ρ hu hρ
  apply (h u t ρ hu hρ).trans
  apply mul_le_mul' _ le_rfl
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg _))

lemma strongTower_mono {d L L' g g' : ℝ} {B B' n : ℕ} {x v : Fin n → Space}
    (hd : 0 < d) (hd1 : d ≤ 1) (hL : L ≤ L') (hg : g ≤ g') (hB : B ≤ B')
    (h : StrongTower d L g B n x v) : StrongTower d L' g' B' n x v := by
  obtain ⟨J, hJ, hJB, r, N, y, w, f, hr0, hrJ, hN0, hleaf, hunit, hedge, hlocal⟩ := h
  refine ⟨J, hJ, hJB.trans hB, r, N, y, w, f, hr0, hrJ, hN0, hleaf, hunit, ?_, ?_⟩
  · intro j hj
    obtain ⟨hs, hsr, hgap, hsub⟩ := hedge j hj
    refine ⟨hs, hsr, ?_, hsub⟩
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 hg) (hs.le.trans hsr.le)).trans hgap
  · intro j hj k
    exact ⟨fiberCount_mono (hlocal j hj k).1 hL, fiberSlab_mono (hlocal j hj k).2 hL⟩

/-- When the requested exponent increases, every existing tower remains usable. -/
theorem depth_step_of_gap_le {σ ω : ℝ} {q : ℕ}
    (hgap : Gap ω q ≤ Gap ω (q + 1)) (h : Depth σ ω q) : Depth σ ω (q + 1) := by
  intro ε D hε hD
  obtain ⟨α, hα, κ, hκ, η, hη, hdata⟩ := h ε D hε hD
  refine ⟨α, hα, κ, hκ, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hA
  rcases hdata δ hδ hδ100 n x v Y hA with hQ | ⟨hDδ, m, x', v', Y', M, L, hA', hsub, hmass, hG⟩
  · exact Or.inl hQ
  · exact Or.inr ⟨hDδ, m, x', v', Y', M, L, hA', hsub, hmass,
      strongTower_mono hδ (by linarith) le_rfl hgap (by simp [pow_succ]) hG⟩

/-- The local fibre estimate and covering alternative supplied to the induction step. -/
abbrev LocalAlternatives (σ ω : ℝ) : Prop := (∀ ζ : ℝ, 0<ζ → ∃ α κ : ℝ, 0<α ∧ 0<κ ∧ ∀ ε : ℝ, 0<ε → ∃ a η c C : ℝ, 0<a ∧ 0<η ∧ 0<c ∧ 1≤C ∧ ∀ r s : ℝ, 0<s → s≤c*r → r≤1 → ∀ y w, ‖w‖=1 → ∀ n x v Y, Fiber r s η y w n x v Y → ENNReal.ofReal (a*(s/r)^(ω+ε)*(n*s^2)*(n*(s/r))^(-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) ∧ (ENNReal.ofReal (κ*(s/r)^(ω-α)*(n*s^2)*(n*(s/r))^(-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) ∨ ∃ (S : Finset (Fin n)) (Z : Fin n → Set _) (ρ : ℝ) (N : ℕ) (y' w' : Fin N → _) (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧ ENNReal.ofReal ((s/r)^ζ)*(∑ i, MeasureTheory.volume (Y i)) ≤ ∑ i ∈ S, MeasureTheory.volume (Z i) ∧ r*(s/r)^(1-ω/100)≤C*ρ ∧ ρ≤C*(r*(s/r)^(ω/100)) ∧ (∀ k, ‖w' k‖=1 ∧ Tube ρ (y' k) (w' k) ⊆ Tube (2*r) y w) ∧ (∀ i ∈ S, Tube s (x i) (v i) ⊆ Tube (2*ρ) (y' (f i)-(1/2 : ℝ) • w' (f i)) (2 • w' (f i))) ∧ FiberCount ρ ((s/r)^(-ζ)) N (fun _ => True) (fun k => Tube ρ (y' k) (w' k)) ∧ FiberSlab r y w ((s/r)^(-ζ)) N (fun _ => True) (fun k => Tube ρ (y' k) (w' k)) ∧ ∀ k, FiberSlab ρ (y' k) (w' k) ((s/r)^(-ζ)) n (fun i => i ∈ S ∧ f i=k) (fun i => Tube s (x i) (v i))))

end

end WangZahlLot.Obl.wz_tower_depth_step
