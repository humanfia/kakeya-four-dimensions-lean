import Submission.Obl.k4_true_forest_own_depth_preparation.LayerPruning

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- Apply the accepted one-layer cutoff at each fixed actual depth, keeping
one common polynomial format for all levels. -/
theorem prune_layers {N κ θ L τ c₀ : ℝ} {W C m M D Mb : ℕ}
    (hN : 2 ≤ N) (hκ : 1 ≤ κ) (hκθ : κ ≤ θ)
    (ω : Fin W → ℝ) (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (ν : Fin W → Measure Line) (hν : ∀ w, IsProbabilityMeasure (ν w))
    (E : Fin W → Set Inc) (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (B : Fin W → ℝ) (hB : ∀ w, 0 < B w) (hBmax : ∀ w, B w ≤ N ^ Mb)
    (r : ℕ → ℝ) (hr : ∀ i, i < m → r i ≤ L) (f : ℝ → ℝ)
    (g : Fin W → ℝ → Obs → ENNReal)
    (hg : ∀ i, i < m → ∀ w, Measurable (g w (r i)))
    (hlaw : ∀ i, i < m → ∀ w,
      (selected (ν w) (E w)).map (obs (B w) (δ N (r i))) =
        (volume.prod Measure.count).withDensity (g w (r i)))
    (htyp : ∀ i, i < m → ∑ w, ENNReal.ofReal (ω w) * selected (ν w) (E w)
      {p | ENNReal.ofReal (N ^ (-f (r i) + τ)) < g w (r i) (obs (B w) (δ N (r i)) p)} ≤
      ENNReal.ofReal (N ^ (-c₀)))
    (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (a u : Fin C → E2) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set Line) (F : Fin C → Set Inc)
    (hC : (C : ℝ) ≤ N ^ M) (hlev : ∀ b, lev b < m)
    (hj : ∀ b, j b < 2 ^ T (lev b))
    (hdisj : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b'))
    (hc : ∀ b, chart N M D κ (T (lev b)) (j b : ℝ) (r (lev b))
      (B (γ b)) (E (γ b)) (a b) (u b) (Q b) (R b) (A b) (F b)
      (ENNReal.ofReal (N ^ (-f (r (lev b))) * |(Q b).det| /
        ((2 : ℝ) ^ T (lev b) * κ)) ≤ ((ν (γ b)).prod volume) (F b))) :
    ∃ (H : Fin C → Set Inc) (lst : ℕ → Fin W → Obs → Finset (Fin C)),
      (∀ b, H b ⊆ F b) ∧ (∀ i w o, ((lst i w o).card : ℝ) ≤ θ) ∧
      (∀ b, chart N (prunedExponent M Mb L) (max D 4) θ
        (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) (E (γ b))
        (a b) (u b) (Q b) (R b) (A b) (H b)
        (∀ p ∈ H b, b ∈ lst (lev b) (γ b) (obs (B (γ b)) (δ N (r (lev b))) p))) ∧
      (∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b \ H b)) ≤
        (m : ENNReal) * ENNReal.ofReal (2 * N ^ (-c₀) + 1024 * κ ^ 5 * N ^ τ / θ) := by
  classical
  let Idx := fun i : Fin m => {b : Fin C // lev b = i.val}
  let J (i : Fin m) (b : Idx i) : Fin (2 ^ T i.val) :=
    ⟨j b.val, by simpa only [b.property] using hj b.val⟩
  have hc' (i : Fin m) (b : Idx i) :
      chart N M D κ (T i.val) ((J i b : ℕ) : ℝ) (r i.val)
        (B (γ b.val)) (E (γ b.val)) (a b.val) (u b.val) (Q b.val) (R b.val)
        (A b.val) (F b.val)
        (ENNReal.ofReal (N ^ (-f (r i.val)) * |(Q b.val).det| /
          ((2 : ℝ) ^ T i.val * κ)) ≤ ((ν (γ b.val)).prod volume) (F b.val)) := by
    simpa only [b.property] using hc b.val
  have hd' (i : Fin m) (b b' : Idx i) (hne : b ≠ b') (hγ : γ b.val = γ b'.val)
      (hJ : J i b = J i b') : Disjoint (A b.val) (A b'.val) :=
    hdisj b.val b'.val (fun h => hne (Subtype.ext h))
      (b.property.trans b'.property.symm) hγ (congrArg Fin.val hJ)
  have hcard (i : Fin m) : (Fintype.card (Idx i) : ℝ) ≤ N ^ M := by
    apply le_trans _ hC
    have hn : Fintype.card (Idx i) ≤ C := by
      simpa only [Idx, Fintype.card_fin] using
        Fintype.card_subtype_le (fun b : Fin C => lev b = i.val)
    exact_mod_cast hn
  have hex (i : Fin m) := prune_finite_layer hN hκ hκθ ω hω0 hω1 ν hν E hE B hB hBmax
    (fun w => g w (r i.val)) (hg i.val i.isLt) (hlaw i.val i.isLt)
    (fun b : Idx i => γ b.val) (J i) (fun b => a b.val) (fun b => u b.val)
    (fun b => Q b.val) (fun b => R b.val) (fun b => A b.val) (fun b => F b.val)
    (hcard i) (hd' i) (hc' i) (htyp i.val i.isLt)
  choose H₁ lst₁ hsub hlist hchart hloss using hex
  let H : Fin C → Set Inc := fun b => H₁ ⟨lev b, hlev b⟩ ⟨b, rfl⟩
  let lst : ℕ → Fin W → Obs → Finset (Fin C) := fun i w o =>
    if hi : i < m then (lst₁ ⟨i, hi⟩ w o).map (Function.Embedding.subtype _) else ∅
  have hH (i : Fin m) (b : Idx i) : H b.val = H₁ i b := by
    rcases b with ⟨b, hb⟩
    have hi : (⟨lev b, hlev b⟩ : Fin m) = i := Fin.ext hb
    cases hi
    rfl
  have hN1 : 1 ≤ N := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (by linarith : 0 < κ) hκθ
  refine ⟨H, lst, ?_, ?_, ?_, ?_⟩
  · intro b
    exact hsub ⟨lev b, hlev b⟩ ⟨b, rfl⟩
  · intro i w o
    dsimp only [lst]
    split_ifs with hi
    · simpa only [Finset.card_map] using hlist ⟨i, hi⟩ w o
    · simpa using hθ0.le
  · intro b
    let i : Fin m := ⟨lev b, hlev b⟩
    let b₁ : Idx i := ⟨b, rfl⟩
    have hM : prunedExponent M Mb (r (lev b)) ≤ prunedExponent M Mb L := by
      dsimp only [prunedExponent]
      have := Nat.ceil_mono (hr (lev b) (hlev b))
      omega
    apply Submission.Obl.k4_quadratic_atlas_normalization.chart_mono hN1 hM le_rfl
      hθ0 le_rfl (hB (γ b)).le (hchart i b₁)
    intro hx p hp
    dsimp only [lst]
    rw [dif_pos (hlev b)]
    exact Finset.mem_map.mpr ⟨b₁, hx p hp, rfl⟩
  · let levFin : Fin C → Fin m := fun b => ⟨lev b, hlev b⟩
    let mass : Fin C → ENNReal := fun b =>
      ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b \ H b)
    change (∑ b, mass b) ≤ _
    rw [← Finset.sum_fiberwise Finset.univ levFin mass]
    have hs (i : Fin m) : (∑ b ∈ Finset.univ.filter (fun b => levFin b = i), mass b) =
        ∑ b : Idx i, mass b.val := by
      exact Finset.sum_subtype _ (fun b => by simp [levFin, Fin.ext_iff]) mass
    simp_rw [hs]
    calc
      _ ≤ ∑ i : Fin m, ENNReal.ofReal (2 * N ^ (-c₀) + 1024 * κ ^ 5 * N ^ τ / θ) := by
        apply Finset.sum_le_sum
        intro i _
        have := hloss i
        simpa only [mass, hH] using this
      _ = _ := by simp [nsmul_eq_mul]

end Submission.Obl.k4_true_forest_own_depth_preparation
