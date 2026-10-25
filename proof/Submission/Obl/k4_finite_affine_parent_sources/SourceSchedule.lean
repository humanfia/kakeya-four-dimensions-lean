-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceComponents
import Submission.Obl.k4_fixed_menu_density_pruning.Outer

/-!
# Eventual facts of a late sample for the selection schedule

The frozen problem's typicality estimates hold at each fixed depth (pure density) or velocity
width (angular density) eventually with a positive power; at finitely many depths or widths they
hold eventually with ONE common power (accepted `finite_common_power_tail`). The pure-density
version is the accepted `prob_fixed_depth_upper_tails`; `prob_angular_upper_tails` is its
angular analogue.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Filter

noncomputable section

section Problem

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {f : ℝ → ℝ} {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}

/-- The angular upper tails at finitely many velocity widths have one common decay power. -/
theorem prob_angular_upper_tails {ι : Type*} [Fintype ι]
    (hp : prob N K L d S η W ω ν E P B f g G)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i ∧ u i ≤ η * L) {τ : ℝ} (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ i,
      (∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod volume).restrict (E k γ))
        {p | ENNReal.ofReal (N k ^ (-f L - S * u i + τ)) <
          G k γ (u i) ((k4_quadratic_finite_greedy_cover.obs (B k γ)
            (k4_quadratic_finite_greedy_cover.δ (N k) L) p,
            fun j : Fin 2 => ⌊(k4_quadratic_finite_greedy_cover.v p.1) j /
              (k4_quadratic_finite_greedy_cover.δ (N k) (u i))⌋))}) ≤
        ENNReal.ofReal (N k ^ (-c)) := by
  rcases hp with ⟨hN, _, _, _, _, _, _, _, _, _, _, _, _, _, hang⟩
  apply k4_fixed_menu_density_pruning.finite_common_power_tail N
    (fun k => le_trans (by norm_num) (hN k))
  intro i
  exact hang (u i) τ (hu i).1 (hu i).2 hτ

/-- The model loss of the problem is eventually below any positive power. -/
theorem prob_K_eventually (hp : prob N K L d S η W ω ν E P B f g G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, K k ≤ N k ^ ε :=
  hp.2.2.1.2 ε hε

end Problem

/-- The weighted original mass of the ANGULAR upper exception at velocity width `w` with
tolerance `τ`, of one sample (the angular field of the frozen problem). -/
def angularTail (Nk L S : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (G : Fin W → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (τ w : ℝ) : ENNReal :=
  ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ))
    {p | ENNReal.ofReal (Nk ^ (-f L - S * w + τ)) <
      G γ w ((k4_quadratic_finite_greedy_cover.obs (B γ)
        (k4_quadratic_finite_greedy_cover.δ Nk L) p,
        fun j : Fin 2 => ⌊(k4_quadratic_finite_greedy_cover.v p.1) j /
          (k4_quadratic_finite_greedy_cover.δ Nk w)⌋))}

/-- The weighted original mass of the LOWER pure-density exception at the terminal depth `L`
with tolerance `τ`, of one sample. -/
def lowerTail (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (τ : ℝ) : ENNReal :=
  ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w))
    {p | g w L (k4_quadratic_finite_greedy_cover.obs (B w)
      (k4_quadratic_finite_greedy_cover.δ Nk L) p) < ENNReal.ofReal (Nk ^ (-f L - τ))}

/-- **The lateness facts of one sample**, as provided by the outer schedule of
`SourceSelectionSpec`: pure-density upper tails on a fixed depth menu `q` and the lower tail at
the terminal depth `L` (tolerance `τd`, power `cd`), angular upper tails on a fixed width menu `w` (tolerance `τa`, power `ca`),
`N₀ ≤ Nk`, the problem's loss `Kk ≤ Nk^eK`, and finitely many largeness facts `C l ≤ Nk^(a l)`. -/
structure LateFacts (Nk Kk L S : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : Fin W → ℝ) (f : ℝ → ℝ) (g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : Fin W → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    {Gd Ga Gc : ℕ} (q : Fin Gd → ℝ) (τd cd : ℝ) (w : Fin Ga → ℝ) (τa ca : ℝ)
    (N₀ eK : ℝ) (a C : Fin Gc → ℝ) : Prop where
  pure : ∀ i, k4_fixed_menu_density_pruning.upperTail Nk W ω ν E B f g τd (q i) ≤
    ENNReal.ofReal (Nk ^ (-cd))
  lower : lowerTail Nk L W ω ν E B f g τd ≤ ENNReal.ofReal (Nk ^ (-cd))
  angular : ∀ j, angularTail Nk L S W ω ν E B f G τa (w j) ≤ ENNReal.ofReal (Nk ^ (-ca))
  N_ge : N₀ ≤ Nk
  K_le : Kk ≤ Nk ^ eK
  big : ∀ l, C l ≤ Nk ^ (a l)

section Problem

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {f : ℝ → ℝ} {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}

/-- **The lateness facts hold eventually**, with positive tail powers chosen after the menus,
tolerances and constants. -/
theorem exists_lateFacts (hp : prob N K L d S η W ω ν E P B f g G) {Gd Ga Gc : ℕ}
    (q : Fin Gd → ℝ) (hq : ∀ i, q i ∈ Icc 0 L) {τd : ℝ} (hτd : 0 < τd)
    (w : Fin Ga → ℝ) (hw : ∀ j, 0 < w j ∧ w j ≤ η * L) {τa : ℝ} (hτa : 0 < τa)
    (N₀ : ℝ) {eK : ℝ} (heK : 0 < eK) (a C : Fin Gc → ℝ) (ha : ∀ l, 0 < a l) :
    ∃ cd ca : ℝ, 0 < cd ∧ 0 < ca ∧ ∀ᶠ k in atTop,
      LateFacts (N k) (K k) L S (W k) (ω k) (ν k) (E k) (B k) f (g k) (G k) q τd cd w τa ca
        N₀ eK a C := by
  obtain ⟨cd₁, hcd₁, hd⟩ :=
    k4_fixed_menu_density_pruning.prob_fixed_depth_upper_tails hp q hq hτd
  have hL : 0 ≤ L := hp.2.2.2.1.le
  obtain ⟨c₂, hc₂, hlow⟩ : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      lowerTail (N k) L (W k) (ω k) (ν k) (E k) (B k) f (g k) τd ≤
        ENNReal.ofReal (N k ^ (-c)) := by
    have hp' := hp
    rcases hp' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, htail, _⟩
    obtain ⟨c, hc, ht⟩ := htail L τd hL le_rfl hτd
    refine ⟨c, hc, ht.mono fun k hk => le_trans ?_ hk⟩
    unfold lowerTail
    apply Finset.sum_le_sum
    intro w _
    exact mul_le_mul' le_rfl (measure_mono fun _ hp => Or.inl hp)
  obtain ⟨ca, hca, ha'⟩ := prob_angular_upper_tails hp w hw hτa
  have hNt : Tendsto N atTop atTop := hp.2.1
  have hN₀ : ∀ᶠ k in atTop, N₀ ≤ N k := hNt.eventually_ge_atTop N₀
  have hK := prob_K_eventually hp heK
  have hbig : ∀ᶠ k in atTop, ∀ l, C l ≤ N k ^ (a l) :=
    Filter.eventually_all.2 fun l => eventually_rpow_ge hNt (ha l)
  have hN1 : ∀ k, 1 ≤ N k := fun k => le_trans (by norm_num) (hp.1 k)
  have hmono : ∀ k (c c' : ℝ), c' ≤ c → ENNReal.ofReal (N k ^ (-c)) ≤ ENNReal.ofReal (N k ^ (-c')) :=
    fun k c c' h => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith))
  refine ⟨min cd₁ c₂, ca, lt_min hcd₁ hc₂, hca, ?_⟩
  filter_upwards [hd, hlow, ha', hN₀, hK, hbig] with k h1 h1' h2 h3 h4 h5
  exact ⟨fun i => (h1 i).trans (hmono k _ _ (min_le_left _ _)),
    h1'.trans (hmono k _ _ (min_le_right _ _)), h2, h3, h4, h5⟩

end Problem

end

end Submission.Obl.k4_finite_affine_parent_sources
