-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyAt.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyLevel
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Branches
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Assembly
-- Copied from session x0338 (o070 branch, commit ec01e52, file StickyAt.lean), namespace renamed.

/-!
# The sticky branch at a fixed scale

`sticky_branch_at` proves the conclusion of x0305's `StickyBranchStmt` at one scale `δ`, under
explicit numerical hypotheses (all of the form `const ≤ δ^(-p)` with `p > 0` once the parameters
are fixed; `StickyBranch.lean` chooses the parameters and makes `δ` small).

Proof: run `iterate_levels` over the levels `k ≤ top` with the good sets of
`sticky_fibre_dichotomy` (Katz–Tao with the round-box constant of the sticky profile).
* A flat-dominated level `k`: the flat cells, whole cells of the current set, each carry a flat
  `LongFactor`, and x0305's `flat_exit_of_cells` gives frozen `SC`.
* Otherwise every cell of every level lies in a Katz–Tao set, and `sticky_allScales_of_refined`
  (threshold cleanup and x0305's `allScales_of_prepared`) gives frozen `S`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- `(2 δ^(-ν))^n ≤ 2^N δ^(-ν N)` for `n ≤ N`. -/
lemma two_pow_mul_rpow_le {δ ν : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) {n N : ℕ}
    (hnN : n ≤ N) : (2 * δ ^ (-ν)) ^ n ≤ 2 ^ N * δ ^ (-(ν * N)) := by
  have h1 : (1 : ℝ) ≤ δ ^ (-ν) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  rw [mul_pow]
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hnN
  have h3 : (δ ^ (-ν)) ^ n ≤ δ ^ (-(ν * N)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    nlinarith
  exact mul_le_mul h2 h3 (by positivity) (by positivity)

open Classical in
/-- **The sticky branch at a fixed scale.** -/
theorem sticky_branch_at {ξ ζ₂ ζ₃ ω ν ζF θ e : ℝ} (hξ : 0 < ξ) (hζ₂ : 0 ≤ ζ₂) (hζ₂ξ : ζ₂ ≤ ξ)
    (hν : 0 < ν) (hζF : 0 ≤ ζF) {Nmax : ℕ}
    {δ : ℝ} (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100) (hdich : FibreDich ν δ)
    {L top : ℕ} (hL : 2 ≤ L) (hLup : (L : ℝ) ≤ δ ^ (-(ζ₂ / 16))) (htopN : top + 1 ≤ Nmax)
    (htop1 : 2 * δ * (L : ℝ) ^ top ≤ 1 / 10000) (htop2 : δ ^ (ξ / 2) ≤ 2 * δ * (L : ℝ) ^ top)
    {m : ℕ} (x v : Fin m → Sp) (S : Finset (Fin m)) (a : ℕ → ℕ)
    (hprep : Prepared δ L top x v S a (δ ^ (-ζF)))
    (hst : ∀ i j, i ≤ j → j ≤ top →
      cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top i - ξ / 2 ≤
        cellProfile δ a (fun k => 2 * δ * (L : ℝ) ^ k) top j)
    -- numerical hypotheses
    (hpig : ∀ n' : ℕ, n' ≤ m → (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
        (Nat.log 2 ⌊(n' : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν))
    (htwo : (2 : ℝ) ≤ δ ^ (-ξ))
    (hbalc : 4 * δ ^ (-e) ≤ δ ^ (-ξ))
    (hsmall : 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * (((Nmax : ℝ) + 1) * δ ^ e) ≤ 1)
    (hKM : 2 * δ ^ (-ζF) * (2 ^ Nmax * δ ^ (-(ν * Nmax))) ≤ δ ^ (-ξ))
    (hcρ : 1600 * (122 ^ 3 * 16 ^ 3) * δ ^ (-(ζ₂ / 8)) * (16 * δ ^ (-ν - ζ₂ / 200)) *
      (1 / δ) ^ (ξ / 2) * δ ^ (-ν) ≤ δ ^ (-ξ) * δ ^ e)
    (hcountKT : 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω ≤ 1)
    (h64 : 64 * δ ^ ν ≤ 1) (hretain : 2 * δ ^ (θ - 2 * ν) ≤ 1)
    (herror : localFlatLoss * δ ^ (ζ₃ - (ζF + ν * (Nmax + 1)) - 5 * (2 * ν)) ≤ 1)
    (hFBc : 2 * 2 ^ Nmax ≤ δ ^ (-ν))
    (hcountF : 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω ≤ δ ^ θ) :
    ∃ (k : ℕ) (g : Fin k → Fin m), Function.Injective g ∧ (∀ j, g j ∈ S) ∧
      δ ^ ω * S.card ≤ k ∧
      (AllScales ξ δ (fun j => x (g j)) (fun j => v (g j)) ∨
        FlatPrisms ζ₂ ζ₃ δ
          (fun j => Metric.thickening δ (segment ℝ (x (g j)) (x (g j) + v (g j))))) := by
  obtain ⟨hv, hT, hsep, hcan, hanti, hSne, hcls, hpopS, hFS⟩ := hprep
  have hδ1 : δ < 1 := by linarith
  have hδ1' : δ ≤ 1 := hδ1.le
  set ρ : ℕ → ℝ := fun k => 2 * δ * (L : ℝ) ^ k with hρdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (le_trans (by norm_num) hL)
  have hρpos : ∀ k, 0 < ρ k := fun k => by simp only [hρdef]; positivity
  have hρmono : ∀ k k', k ≤ k' → ρ k ≤ ρ k' := fun k k' hkk => by
    simp only [hρdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 hkk) (by positivity)
  set Λ : ℝ := 16 * δ ^ (-ν - ζ₂ / 200) with hΛdef
  have hΛ1 : 1 ≤ Λ := by
    have : (1 : ℝ) ≤ δ ^ (-ν - ζ₂ / 200) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1' (by linarith)
    rw [hΛdef]
    linarith
  set c : ℕ → ℝ := fun k => stickyK δ L Λ (ξ / 2) a ρ k * δ ^ (-ν) with hcdef
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    have h1 := stickyK_nonneg (c := ξ / 2) (L := (L : ℝ)) (Λ := Λ) hδ (by linarith) a hρpos k
    exact mul_nonneg h1 (Real.rpow_nonneg hδ.le _)
  set κ : ℕ → Fin m → (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
    fun k i => lineCell (ρ k / 20) (x i) (v i) with hκdef
  set G : ℕ → Finset (Fin m) → Prop := fun k F' => ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (((F'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal (c k) * volume W with hGdef
  set lam : ℝ := δ ^ (-ν) with hlamdef
  have hlam : 1 ≤ lam := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1' (by linarith)
  have hM : ∀ n, n ≤ Nmax → (2 * lam) ^ n ≤ 2 ^ Nmax * δ ^ (-(ν * Nmax)) := fun n hn =>
    two_pow_mul_rpow_le hδ hδ1' hν.le hn
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  rcases iterate_levels κ G hlam S (top + 1) with
    ⟨k, hk, S', hS'S, hcard', hflat⟩ | ⟨S₁, hS₁S, hcard₁, hgood⟩
  · ------------------------------------------------------------------ flat-dominated level
    have hk' : k ≤ top := by omega
    set B := S'.filter (fun i => flatP (G k) lam (fibre S' (κ k) i)) with hBdef
    have hBS' : B ⊆ S' := Finset.filter_subset _ _
    have hMk : (2 * lam) ^ k ≤ 2 ^ Nmax * δ ^ (-(ν * Nmax)) := hM k (by omega)
    have hSB : (S.card : ℝ) ≤ 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * B.card := by
      have h1 : (S'.card : ℝ) ≤ 2 * B.card := by exact_mod_cast hflat
      calc (S.card : ℝ) ≤ (2 * lam) ^ k * S'.card := hcard'
        _ ≤ (2 ^ Nmax * δ ^ (-(ν * Nmax))) * (2 * B.card) := by
            apply mul_le_mul hMk h1 (Nat.cast_nonneg _) (by positivity)
        _ = 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * B.card := by ring
    have hBne : B.Nonempty := by
      rw [← Finset.card_pos]
      by_contra h0
      push Not at h0
      have : B.card = 0 := by omega
      rw [this, Nat.cast_zero, mul_zero] at hSB
      linarith
    have hS'ne : S'.Nonempty := hBne.mono hBS'
    have hBS : B ⊆ S := hBS'.trans hS'S
    have hρk : 2 * δ ≤ ρ k := by
      have := hρmono 0 k (Nat.zero_le _)
      simpa [hρdef] using this
    have hρk1 : ρ k ≤ 1 / 10000 := (hρmono k top hk').trans htop1
    obtain ⟨k₂, g, hg, hgB, hk₂, hFP⟩ := flat_exit_of_cells (δ := δ) (ρ := ρ k) (ν := ν)
      (Λ := Λ) (ζ := ζF + ν * (Nmax + 1)) (ζ₂ := ζ₂) (ζ₃ := ζ₃) (θ := θ) hδ hδ1' hν.le
      (by positivity) hζ₂ hρk hρk1 le_rfl h64 herror hretain x v hv hT hcan hanti S' hS'ne
      (fun i hi i' hi' => hcls k hk' i (hS'S hi) i' (hS'S hi')) B hBS' hBne
      (fun i hi j hj hji => by
        refine Finset.mem_filter.mpr ⟨hj, ?_⟩
        have hfib : fibre S' (κ k) j = fibre S' (κ k) i := by
          unfold fibre
          simp only [hκdef]
          rw [hji]
        rw [hfib]
        exact (Finset.mem_filter.mp hi).2)
      (fun i hi => by
        have hiS' := (Finset.mem_filter.mp hi).1
        have hfl := (Finset.mem_filter.mp hi).2
        set F := fibre S' (κ k) i with hF
        have hFne : F.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hiS', rfl⟩⟩
        have hFcell : F ⊆ fibre S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i :=
          fun j hj => by
            obtain ⟨hjS', hji⟩ := Finset.mem_filter.mp hj
            exact Finset.mem_filter.mpr ⟨hS'S hjS', hji⟩
        rcases sticky_fibre_dichotomy hδ hδ1 hΛ1 hdich hL htop1 x v hv hT hsep hanti S a
            (fun k hk i hi => (hpopS k hk i hi).2) hst k hk' F hFne i (hS'S hiS') hFcell with
          hKT | hLF
        · exfalso
          apply hfl
          obtain ⟨F', hF'F, hcardF', hKTF'⟩ := hKT
          exact ⟨F', hF'F, hcardF', hKTF'⟩
        · exact hLF)
      (fun W hW => by
        have h := frostman_of_subset x v S B hBS (by positivity : (0 : ℝ) ≤ δ ^ (-ζF)) hSB
          hFS W hW
        refine h.trans ?_
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        calc δ ^ (-ζF) * (2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))))
            = δ ^ (-ζF) * (2 * 2 ^ Nmax) * δ ^ (-(ν * Nmax)) := by ring
          _ ≤ δ ^ (-ζF) * δ ^ (-ν) * δ ^ (-(ν * Nmax)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFBc (by positivity))
                (by positivity)
          _ = δ ^ (-(ζF + ν * (Nmax + 1))) := by
              rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
              congr 1
              ring)
      (hpig B.card ((Finset.card_le_card hBS).trans (Finset.card_le_univ S |>.trans
        (by simp))))
    refine ⟨k₂, g, hg, fun j => hBS (hgB j), ?_, Or.inr hFP⟩
    calc δ ^ ω * S.card ≤ δ ^ ω * (2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * B.card) :=
          mul_le_mul_of_nonneg_left hSB (Real.rpow_nonneg hδ.le _)
      _ = (2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω) * B.card := by ring
      _ ≤ δ ^ θ * B.card := mul_le_mul_of_nonneg_right hcountF (Nat.cast_nonneg _)
      _ ≤ k₂ := hk₂
  · ------------------------------------------------------------------ every level Katz–Tao
    have hM₁ : (2 * lam) ^ (top + 1) ≤ 2 ^ Nmax * δ ^ (-(ν * Nmax)) := hM (top + 1) htopN
    have hM₁pos : 0 < (2 * lam) ^ (top + 1) := by positivity
    obtain ⟨S₂, hS₂S₁, hS₂ne, hS₂card, hAS⟩ := sticky_allScales_of_refined (e := e)
      (K := δ ^ (-ζF)) (M₁ := (2 * lam) ^ (top + 1)) hδ hδ1' hξ (by positivity) hM₁pos hL
      (hLup.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith))) htwo htop1
      ((Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith)).trans htop2)
      x v hv hT hcan hanti a S (fun k hk => hcls k hk) (fun k hk => hpopS k hk) hFS S₁ hS₁S
      hcard₁ c hc0
      (fun k hk i hi => by
        obtain ⟨F', hF', hG⟩ := hgood k (by omega) i hi
        exact ⟨F', hF', hG⟩)
      (by
        calc 2 * (2 * lam) ^ (top + 1) * (((top : ℝ) + 1) * δ ^ e)
            ≤ 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * (((Nmax : ℝ) + 1) * δ ^ e) := by
              have htN : (top : ℝ) + 1 ≤ (Nmax : ℝ) + 1 := by
                have : (top : ℝ) + 1 ≤ Nmax := by exact_mod_cast htopN
                linarith
              apply mul_le_mul (mul_le_mul_of_nonneg_left hM₁ (by norm_num))
                (mul_le_mul_of_nonneg_right htN (Real.rpow_nonneg hδ.le _))
                (by positivity) (by positivity)
          _ ≤ 1 := hsmall)
      hbalc
      (by
        calc 2 * δ ^ (-ζF) * (2 * lam) ^ (top + 1)
            ≤ 2 * δ ^ (-ζF) * (2 ^ Nmax * δ ^ (-(ν * Nmax))) :=
              mul_le_mul_of_nonneg_left hM₁ (by positivity)
          _ ≤ δ ^ (-ξ) := hKM)
      (fun k hk => by
        -- `c k ρ_k² = 800 C₀ L² Λ (1/δ)^(ξ/2) 2^(a k) δ² δ^(-ν)`
        have hρk := hρpos k
        have hρ2 : ρ k ^ 2 ≠ 0 := by positivity
        have hL2 : ((L : ℝ)) ^ 2 ≤ δ ^ (-(ζ₂ / 8)) := by
          calc ((L : ℝ)) ^ 2 ≤ (δ ^ (-(ζ₂ / 16))) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hLup 2
            _ = δ ^ (-(ζ₂ / 8)) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
                congr 1; push_cast; ring
        have hck : c k * (2 * δ * (L : ℝ) ^ k) ^ 2 =
            (800 * (122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * Λ * (1 / δ) ^ (ξ / 2) * δ ^ (-ν)) *
              (δ ^ 2 * ((2 ^ a k / ρ k ^ 2) * ρ k ^ 2)) := by
          show stickyK δ L Λ (ξ / 2) a ρ k * δ ^ (-ν) * ρ k ^ 2 = _
          unfold stickyK levelDens
          ring
        rw [hck, div_mul_cancel₀ _ hρ2]
        have hA : 0 ≤ (1 / δ) ^ (ξ / 2) * δ ^ (-ν) := by positivity
        have h1 : 800 * (122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * Λ * (1 / δ) ^ (ξ / 2) * δ ^ (-ν)
            ≤ 800 * (122 ^ 3 * 16 ^ 3) * δ ^ (-(ζ₂ / 8)) * Λ * (1 / δ) ^ (ξ / 2) * δ ^ (-ν) := by
          have e1 : 800 * (122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * Λ * (1 / δ) ^ (ξ / 2) * δ ^ (-ν) =
              (800 * (122 ^ 3 * 16 ^ 3)) * ((L : ℝ) ^ 2 * (Λ * ((1 / δ) ^ (ξ / 2) * δ ^ (-ν)))) := by
            ring
          have e2 : 800 * (122 ^ 3 * 16 ^ 3) * δ ^ (-(ζ₂ / 8)) * Λ * (1 / δ) ^ (ξ / 2) * δ ^ (-ν) =
              (800 * (122 ^ 3 * 16 ^ 3)) * (δ ^ (-(ζ₂ / 8)) * (Λ * ((1 / δ) ^ (ξ / 2) * δ ^ (-ν)))) := by
            ring
          rw [e1, e2]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hL2 (mul_nonneg (by linarith) hA)
        have h2 : 800 * (122 ^ 3 * 16 ^ 3) * δ ^ (-(ζ₂ / 8)) * Λ * (1 / δ) ^ (ξ / 2) * δ ^ (-ν)
            = (1600 * (122 ^ 3 * 16 ^ 3) * δ ^ (-(ζ₂ / 8)) * (16 * δ ^ (-ν - ζ₂ / 200)) *
              (1 / δ) ^ (ξ / 2) * δ ^ (-ν)) / 2 := by
          rw [hΛdef]; ring
        have key : 800 * (122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * Λ * (1 / δ) ^ (ξ / 2) * δ ^ (-ν)
            ≤ δ ^ (-ξ) * δ ^ e / 2 := by
          rw [h2] at h1
          linarith
        have hpa : (0 : ℝ) ≤ δ ^ 2 * 2 ^ a k := by positivity
        calc (800 * (122 ^ 3 * 16 ^ 3) * (L : ℝ) ^ 2 * Λ * (1 / δ) ^ (ξ / 2) * δ ^ (-ν)) *
              (δ ^ 2 * 2 ^ a k)
            ≤ (δ ^ (-ξ) * δ ^ e / 2) * (δ ^ 2 * 2 ^ a k) := mul_le_mul_of_nonneg_right key hpa
          _ = δ ^ (-ξ) * ((2 : ℝ) ^ a k * δ ^ e / 2) * δ ^ 2 := by ring)
      hSne
    refine ⟨S₂.card, fun j => (S₂.equivFin.symm j).1, fun j j' h => ?_,
      fun j => hS₁S (hS₂S₁ (S₂.equivFin.symm j).2), ?_, Or.inl hAS⟩
    · exact S₂.equivFin.symm.injective (Subtype.ext h)
    · have h1 : (S.card : ℝ) ≤ 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * S₂.card := by
        calc (S.card : ℝ) ≤ 2 * (2 * lam) ^ (top + 1) * S₂.card := hS₂card
          _ ≤ 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * S₂.card :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM₁ (by norm_num))
              (Nat.cast_nonneg _)
      calc δ ^ ω * S.card ≤ δ ^ ω * (2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * S₂.card) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hδ.le _)
        _ = (2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω) * S₂.card := by ring
        _ ≤ 1 * S₂.card := mul_le_mul_of_nonneg_right hcountKT (Nat.cast_nonneg _)
        _ = S₂.card := one_mul _

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
