/- Retained from this obligation, o255, branch x0901 at commit 0f8ba410.
   Earlier source attributions in this file are preserved. -/
import Submission.Obl.k4_general_parent_narrow_contact_transfer.Interface

/-!
# Wide or narrow projected layers

An ordinary projected-layer output whose requested depths all have subpower
narrowness `g_s / β_s` is a wide output after enlarging `H` by the finite
product of these ratios.  So either the wide principle applies, or some
requested depth has a fixed-power narrow subsequence.  This file proves that
dichotomy; the narrow alternative is the hypothesis `core` of
`candidates_of_layers`.
-/

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α]

/-- One requested depth of a projected-layer output, exactly as in the frozen type. -/
def Slice (cfg : Model α) (wide : Bool) (L a m : ℝ) (τ : ℕ → ℕ) (H : ℕ → ℝ)
    (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ) (n' : ℕ → ℝ → ℕ)
    (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
    (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
    (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
    (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ)
    (k : ℕ) (s : ℝ) : Prop :=
  0 < β k s ∧ (cfg.N (τ k) ^ (-cfg.ℓ * s) * (if wide then 1 else cfg.N (τ k) ^ (-L * a))) / H k ≤ β k s ∧ β k s ≤ H k * cfg.N (τ k) ^ (-cfg.ℓ * s) ∧ (∀ i,MeasurableSet (C k s i)) ∧ (∀ i i',i ≠ i' → Disjoint (C k s i) (C k s i')) ∧ (∀ i,|u k s i| + |v k s i| ≤ H k ∧ (G k s i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (0:ℝ) 1,∀ w ∈ Set.Icc (-1:ℝ) 1,|MvPolynomial.eval ![t,u k s i + t * v k s i + β k s * w] (G k s i)| ≤ H k) ∧ (∀ l ∈ C k s i,⌊cfg.b (τ k) l 3 / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0 ∧ ⌊cfg.b (τ k) l 0 / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 1 ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,|(cfg.x (τ k) l t) 2 - u k s i - t * v k s i| ≤ H k * β k s ∧ |MvPolynomial.eval (cfg.x (τ k) l t) (cfg.P (τ k)) - MvPolynomial.eval ![t,(cfg.x (τ k) l t) 2] (G k s i)| ≤ H k * cfg.N (τ k) ^ (-s)) ∧ ENNReal.ofReal (cfg.N (τ k) ^ (-m) * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H k) * cfg.π (τ k) {w:ℝ | ⌊w / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0} ≤ cfg.ρ (τ k) (C k s i ×ˢ Set.Icc (0:ℝ) 1)) ∧ (∑ i:Fin (n' k s),ENNReal.ofReal (cfg.N (τ k) ^ (-m) * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s) * cfg.π (τ k) {w:ℝ | ⌊w / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0}) ≤ ENNReal.ofReal (H k) ∧ (∀ᵐ p ∂ρ' k,∃ i,p.1 ∈ C k s i)

/-- A projected-layer output for fixed `(L, a, D, m)`, exactly as in the frozen type. -/
def LayerOutput (cfg : Model α) (wide : Bool) (L a : ℝ) (D : Finset ℝ) (m : ℝ) : Prop :=
  ∃ τ:ℕ → ℕ,StrictMono τ ∧ ∃ H:ℕ → ℝ,(∀ k,1 ≤ H k ∧ cfg.K (τ k) ≤ H k) ∧ (∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,H k ≤ cfg.N (τ k) ^ ε) ∧ ∃ (ρ':ℕ → MeasureTheory.Measure (α × ℝ)) (β:ℕ → ℝ → ℝ) (n':ℕ → ℝ → ℕ) (C:(k:ℕ) → (s:ℝ) → Fin (n' k s) → Set α) (tag:(k:ℕ) → (s:ℝ) → Fin (n' k s) → Fin 2 → ℤ) (u v:(k:ℕ) → (s:ℝ) → Fin (n' k s) → ℝ) (G:(k:ℕ) → (s:ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),(∀ k,ρ' k ≤ cfg.ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ) ∧ ∀ k s,s ∈ D → Slice cfg wide L a m τ H ρ' β n' C tag u v G k s

theorem layers_iff (cfg : Model α) (wide : Bool) :
    Layers cfg wide ↔ ∃ L:ℝ,2 < L ∧ ∀ a:ℝ,0 < a → (if wide then L else 2) * a < cfg.U → ∀ D:Finset ℝ,(∀ s ∈ D,a ≤ s ∧ s ≤ 2 * a) → ∀ m:ℝ,L * a < m → LayerOutput cfg wide L a D m :=
  Iff.rfl

/-- The narrow alternative at one requested depth `s` of an ordinary output:
`β_s` is smaller than `g_s = N^(-ℓ s)` by a fixed power, frequently. -/
structure NarrowWitness (cfg : Model α) (L a m s : ℝ) (τ : ℕ → ℕ) (H : ℕ → ℝ)
    (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ) (n' : ℕ → ℝ → ℕ)
    (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
    (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
    (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
    (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ) : Prop where
  mono : StrictMono τ
  loss : ∀ k, 1 ≤ H k ∧ cfg.K (τ k) ≤ H k
  loss_subpower : ∀ ε:ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ cfg.N (τ k) ^ ε
  retained : ∀ k, ρ' k ≤ cfg.ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ
  slice : ∀ k, Slice cfg false L a m τ H ρ' β n' C tag u v G k s
  narrow : ∃ e : ℝ, 0 < e ∧
    ∃ᶠ k in Filter.atTop, cfg.N (τ k) ^ e * β k s < cfg.N (τ k) ^ (-cfg.ℓ * s)

/-- Enlarging the loss `H` to cover the narrowness `g_s / β_s` turns an
ordinary slice into a wide one. -/
theorem slice_widen (cfg : Model α) {L L' a m : ℝ} {τ : ℕ → ℕ} {H H' : ℕ → ℝ}
    {ρ' : ℕ → Measure (α × ℝ)} {β : ℕ → ℝ → ℝ} {n' : ℕ → ℝ → ℕ}
    {C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α}
    {tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ}
    {u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ}
    {G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ} {k : ℕ} {s : ℝ}
    (h : Slice cfg false L a m τ H ρ' β n' C tag u v G k s)
    (hN : 0 < cfg.N (τ k)) (hH : 1 ≤ H k) (hHH : H k ≤ H' k)
    (hgap : cfg.N (τ k) ^ (-cfg.ℓ * s) ≤ H' k * β k s) :
    Slice cfg true L' a m τ H' ρ' β n' C tag u v G k s := by
  obtain ⟨hβ, -, hβu, hmeas, hdisj, hi, hsum, hae⟩ := h
  have hH0 : 0 < H k := lt_of_lt_of_le one_pos hH
  have hH'0 : 0 < H' k := lt_of_lt_of_le hH0 hHH
  refine ⟨hβ, ?_, ?_, hmeas, hdisj, ?_, ?_, hae⟩
  · simp only [ite_true, mul_one]
    rw [div_le_iff₀ hH'0]
    linarith [mul_comm (H' k) (β k s)]
  · have hg : 0 ≤ cfg.N (τ k) ^ (-cfg.ℓ * s) := Real.rpow_nonneg hN.le _
    exact hβu.trans (mul_le_mul_of_nonneg_right hHH hg)
  · intro i
    obtain ⟨huv, hdeg, hGb, hl, hmass⟩ := hi i
    refine ⟨huv.trans hHH, hdeg, fun t ht w hw => (hGb t ht w hw).trans hHH, ?_, ?_⟩
    · intro l hlC
      obtain ⟨h1, h2, h3⟩ := hl l hlC
      refine ⟨h1, h2, fun t ht => ⟨?_, ?_⟩⟩
      · exact (h3 t ht).1.trans (mul_le_mul_of_nonneg_right hHH hβ.le)
      · exact (h3 t ht).2.trans
          (mul_le_mul_of_nonneg_right hHH (Real.rpow_nonneg hN.le _))
    · refine le_trans ?_ hmass
      gcongr
  · exact hsum.trans (ENNReal.ofReal_le_ofReal hHH)

/-- `f` grows more slowly than every positive power of `N`. -/
def Subpow (N f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, f k ≤ N k ^ ε

theorem Subpow.mul {N f g : ℕ → ℝ} (hN : ∀ k, 0 < N k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : Subpow N f) (hg : Subpow N g) : Subpow N (fun k => f k * g k) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by linarith), hg (ε / 2) (by linarith)] with k h1 h2
  calc f k * g k ≤ N k ^ (ε / 2) * N k ^ (ε / 2) :=
        mul_le_mul h1 h2 (hg0 k) (Real.rpow_nonneg (hN k).le _)
    _ = N k ^ ε := by rw [← Real.rpow_add (hN k)]; ring_nf

theorem Subpow.finset_prod {ι : Type*} (D : Finset ι) {N : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) {f : ι → ℕ → ℝ} (hf0 : ∀ i k, 0 ≤ f i k)
    (hf : ∀ i ∈ D, Subpow N (f i)) : Subpow N (fun k => ∏ i ∈ D, f i k) := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    intro ε hε
    exact Filter.Eventually.of_forall fun k => by
      simpa using Real.one_le_rpow (hN k) hε.le
  | insert a D ha ih =>
    have hrest : Subpow N (fun k => ∏ i ∈ D, f i k) :=
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hmul := Subpow.mul (fun k => lt_of_lt_of_le one_pos (hN k))
      (fun k => Finset.prod_nonneg fun i _ => hf0 i k)
      (hf a (Finset.mem_insert_self a D)) hrest
    intro ε hε
    filter_upwards [hmul ε hε] with k hk
    rwa [Finset.prod_insert ha]

/-- The dichotomy: either every ordinary output is subpower-wide, and the wide
principle gives the candidates, or some requested depth is narrow by a fixed
power.  `Λ` chooses the wide constant from the ordinary one; the narrow
alternative `core` may use the guard `Λ L₀ * a < U`. -/
theorem candidates_of_layers (cfg : Model α) (hN : ∀ k, 2 ≤ cfg.N k)
    (h0 : Layers cfg false) (h1 : Layers cfg true → cfg.Candidates)
    (Λ : ℝ → ℝ) (hΛ : ∀ L, 2 < L → L ≤ Λ L)
    (core : ∀ L₀ : ℝ, 2 < L₀ →
      (∀ a : ℝ, 0 < a → 2 * a < cfg.U → ∀ D : Finset ℝ, (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) →
        ∀ m : ℝ, L₀ * a < m → LayerOutput cfg false L₀ a D m) →
      ∀ a s m : ℝ, 0 < a → Λ L₀ * a < cfg.U → a ≤ s → s ≤ 2 * a → Λ L₀ * a < m →
      ∀ (τ : ℕ → ℕ) (H : ℕ → ℝ) (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ)
        (n' : ℕ → ℝ → ℕ) (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
        (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
        (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
        (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),
        NarrowWitness cfg L₀ a m s τ H ρ' β n' C tag u v G → cfg.Candidates) :
    cfg.Candidates := by
  by_contra hG
  obtain ⟨L₀, hL₀, hlay⟩ := (layers_iff cfg false).1 h0
  have hlay' : ∀ a : ℝ, 0 < a → 2 * a < cfg.U → ∀ D : Finset ℝ,
      (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) → ∀ m : ℝ, L₀ * a < m →
      LayerOutput cfg false L₀ a D m := fun a ha h2 D hD m hm =>
    hlay a ha (by simpa using h2) D hD m hm
  have hΛ' := hΛ L₀ hL₀
  apply hG
  apply h1
  refine (layers_iff cfg true).2 ⟨Λ L₀, lt_of_lt_of_le hL₀ hΛ', ?_⟩
  intro a ha haU D hD m hm
  simp only [ite_true] at haU
  obtain ⟨τ, hτ, H, hH, hHsub, ρ', β, n', C, tag, u, v, G, hρ', hsl⟩ :=
    hlay' a ha (by nlinarith) D hD m (by nlinarith)
  by_cases hnar : ∃ s ∈ D, ∃ e : ℝ, 0 < e ∧
      ∃ᶠ k in Filter.atTop, cfg.N (τ k) ^ e * β k s < cfg.N (τ k) ^ (-cfg.ℓ * s)
  · exfalso
    obtain ⟨s, hs, e, he, hfreq⟩ := hnar
    exact hG (core L₀ hL₀ hlay' a s m ha haU (hD s hs).1 (hD s hs).2 hm
      τ H ρ' β n' C tag u v G ⟨hτ, hH, hHsub, hρ', fun k => hsl k s hs, e, he, hfreq⟩)
  · push Not at hnar
    have hNpos : ∀ k, 0 < cfg.N k := fun k => lt_of_lt_of_le two_pos (hN k)
    have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => le_trans one_le_two (hN k)
    set f : ℝ → ℕ → ℝ := fun s k => max 1 (cfg.N (τ k) ^ (-cfg.ℓ * s) / β k s) with hf
    have hf1 : ∀ s k, 1 ≤ f s k := fun s k => le_max_left _ _
    have hprod1 : ∀ k, 1 ≤ ∏ s ∈ D, f s k :=
      fun k => Finset.one_le_prod₀ fun s _ => hf1 s k
    have hprodge : ∀ k, ∀ s ∈ D, f s k ≤ ∏ s ∈ D, f s k := by
      intro k s hs
      rw [← Finset.mul_prod_erase D (fun s => f s k) hs]
      exact le_mul_of_one_le_right (le_trans zero_le_one (hf1 s k))
        (Finset.one_le_prod₀ fun s _ => hf1 s k)
    set H' : ℕ → ℝ := fun k => H k * ∏ s ∈ D, f s k with hH'
    have hHH' : ∀ k, H k ≤ H' k := fun k =>
      le_mul_of_one_le_right (le_trans zero_le_one (hH k).1) (hprod1 k)
    refine ⟨τ, hτ, H', fun k => ⟨(hH k).1.trans (hHH' k), (hH k).2.trans (hHH' k)⟩,
      ?_, ρ', β, n', C, tag, u, v, G, fun k => ⟨(hρ' k).1, ?_⟩, ?_⟩
    · have hsubH : Subpow (fun k => cfg.N (τ k)) H := hHsub
      have hsubf : ∀ s ∈ D, Subpow (fun k => cfg.N (τ k)) (f s) := by
        intro s hs e he
        filter_upwards [hnar s hs e he] with k hk
        have hβ : 0 < β k s := (hsl k s hs).1
        refine max_le (Real.one_le_rpow (hN1 _) he.le) ?_
        rw [div_le_iff₀ hβ]
        exact hk
      have := Subpow.mul (fun k => hNpos (τ k))
        (fun k => le_trans zero_le_one (hprod1 k)) hsubH
        (Subpow.finset_prod D (fun k => hN1 (τ k))
          (fun s k => le_trans zero_le_one (hf1 s k)) hsubf)
      exact this
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hρ' k).2
      exact inv_anti₀ (lt_of_lt_of_le one_pos (hH k).1) (hHH' k)
    · intro k s hs
      have hsk := hsl k s hs
      have hβ : 0 < β k s := hsk.1
      refine slice_widen cfg hsk (hNpos _) (hH k).1 (hHH' k) ?_
      have h1 : cfg.N (τ k) ^ (-cfg.ℓ * s) ≤ f s k * β k s := by
        rw [← div_le_iff₀ hβ]
        exact le_max_right _ _
      calc cfg.N (τ k) ^ (-cfg.ℓ * s) ≤ f s k * β k s := h1
        _ ≤ H' k * β k s := by
          apply mul_le_mul_of_nonneg_right _ hβ.le
          calc f s k ≤ ∏ s ∈ D, f s k := hprodge k s hs
            _ ≤ H k * ∏ s ∈ D, f s k :=
              le_mul_of_one_le_left (le_trans zero_le_one (hprod1 k)) (hH k).1

end Model

end

end Submission.Obl.k4_general_parent_narrow_contact_transfer
