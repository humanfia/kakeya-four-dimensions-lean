-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyQ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyBranch
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.CellsQ
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.BranchesQ
-- Copied from session x0338 (o070 branch, commit ec01e52, file StickyQ.lean), namespace renamed.

/-!
# The sticky branch with the quadratic count

`sticky_branch_at_q` and `stickyBranchStmtQ_holds : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.StickyBranchStmtQ` are
`sticky_branch_at` and `stickyBranchStmt_holds` (proofs copied) through `flat_exit_of_cells_q`:
the flat outputs also satisfy the global quadratic count (`FlatPrismsQ`).  One more small-`δ`
condition, `quadLoss δ^(ζ₃ - 16 ν) ≤ 1`, is needed; `16 ν ≤ ζ₃ / 60` here.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open Classical in
/-- `sticky_branch_at` with the quadratic count (extra error bound `herrorQ`). -/
theorem sticky_branch_at_q {ξ ζ₂ ζ₃ ω ν ζF θ e : ℝ} (hξ : 0 < ξ) (hζ₂ : 0 ≤ ζ₂) (hζ₂ξ : ζ₂ ≤ ξ)
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
    (herrorQ : quadLoss * δ ^ (ζ₃ - 8 * (2 * ν)) ≤ 1)
    (hFBc : 2 * 2 ^ Nmax ≤ δ ^ (-ν))
    (hcountF : 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω ≤ δ ^ θ) :
    ∃ (k : ℕ) (g : Fin k → Fin m), Function.Injective g ∧ (∀ j, g j ∈ S) ∧
      δ ^ ω * S.card ≤ k ∧
      (AllScales ξ δ (fun j => x (g j)) (fun j => v (g j)) ∨
        FlatPrismsQ ζ₂ ζ₃ δ
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
    obtain ⟨k₂, g, hg, hgB, hk₂, hFP⟩ := flat_exit_of_cells_q (δ := δ) (ρ := ρ k) (ν := ν)
      (Λ := Λ) (ζ := ζF + ν * (Nmax + 1)) (ζ₂ := ζ₂) (ζ₃ := ζ₃) (θ := θ) hδ hδ1' hν.le
      (by positivity) hζ₂ hρk hρk1 le_rfl h64 herror hretain herrorQ x v hv hT hcan hanti S' hS'ne
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

/-- **The sticky branch with the quadratic count** (`StickyBranchStmtQ`). -/
theorem stickyBranchStmtQ_holds : StickyBranchStmtQ := by
  intro ξ ζ₂ ζ₃ ω hζ₃ hζ₃₂ hζ₂ξ hω Nmax Cp
  have hζ₂ : 0 < ζ₂ := hζ₃.trans_le hζ₃₂
  have hξ : 0 < ξ := hζ₂.trans_le hζ₂ξ
  have hN1 : (1 : ℝ) ≤ (Nmax : ℝ) + 1 := by have := (Nat.cast_nonneg Nmax : (0 : ℝ) ≤ Nmax); linarith
  set N1 : ℝ := (Nmax : ℝ) + 1 with hN1def
  set μ : ℝ := min (min ω ξ) ζ₃ with hμdef
  have hμ : 0 < μ := lt_min (lt_min hω hξ) hζ₃
  have hμω : μ ≤ ω := (min_le_left _ _).trans (min_le_left _ _)
  have hμξ : μ ≤ ξ := (min_le_left _ _).trans (min_le_right _ _)
  have hμζ₃ : μ ≤ ζ₃ := min_le_right _ _
  set ν : ℝ := μ / (1000 * N1) with hνdef
  have hν : 0 < ν := by positivity
  have hνN1 : ν * N1 = μ / 1000 := by rw [hνdef]; field_simp
  have hνle : ν ≤ μ / 1000 := by
    rw [hνdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hνNmax : ν * Nmax ≤ μ / 1000 := by
    have : ν * Nmax ≤ ν * N1 := mul_le_mul_of_nonneg_left (by linarith) hν.le
    linarith
  set ζF : ℝ := min ζ₃ ξ / 8 with hζFdef
  have hζF : 0 < ζF := by positivity
  have hζFξ : ζF ≤ ξ / 8 := by
    rw [hζFdef]; have := min_le_right ζ₃ ξ; linarith
  have hζFζ₃ : ζF ≤ ζ₃ / 8 := by
    rw [hζFdef]; have := min_le_left ζ₃ ξ; linarith
  set θ : ℝ := ω / 2 with hθdef
  set e : ℝ := 2 * N1 * ν with hedef
  have he : e = μ / 500 := by rw [hedef]; linarith [hνN1]
  -- the exponents of the small-`δ` conditions
  have p4 : 0 < ξ - e := by rw [he]; linarith
  have p5 : 0 < e - ν * Nmax := by
    have : e - ν * Nmax = ν * (Nmax + 2) := by rw [hedef, hN1def]; ring
    rw [this]; positivity
  have p6 : 0 < ξ - ζF - ν * Nmax := by linarith
  have p7 : 0 < ξ / 2 - ζ₂ / 8 - ζ₂ / 200 - e - 2 * ν := by rw [he]; linarith
  have p8 : 0 < ω - ν * Nmax := by linarith
  have p10 : 0 < θ - 2 * ν := by rw [hθdef]; linarith
  have p11 : 0 < ζ₃ - (ζF + ν * ((Nmax : ℝ) + 1)) - 5 * (2 * ν) := by
    have : ν * ((Nmax : ℝ) + 1) = μ / 1000 := hνN1
    rw [this]; linarith
  have p13 : 0 < ω - θ - ν * Nmax := by rw [hθdef]; linarith
  have p14 : 0 < ζ₃ - 8 * (2 * ν) := by linarith
  -- thresholds
  obtain ⟨d₁, hd₁, hdich⟩ := fibreDich_of_le ν hν
  obtain ⟨d₂, hd₂, -, hpigE⟩ := flat_exit_pig_eventually ν (max Cp 1) hν (le_max_right _ _)
  obtain ⟨d₃, hd₃, h3⟩ := eventually_le_rpow_neg 2 hξ
  obtain ⟨d₄, hd₄, h4⟩ := eventually_le_rpow_neg 4 p4
  obtain ⟨d₅, hd₅, h5⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax * N1) p5
  obtain ⟨d₆, hd₆, h6⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax) p6
  obtain ⟨d₇, hd₇, h7⟩ := eventually_le_rpow_neg (1600 * (122 ^ 3 * 16 ^ 3) * 16) p7
  obtain ⟨d₈, hd₈, h8⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax) p8
  obtain ⟨d₉, hd₉, h9⟩ := eventually_le_rpow_neg 64 hν
  obtain ⟨d₁₀, hd₁₀, h10⟩ := eventually_le_rpow_neg 2 p10
  obtain ⟨d₁₁, hd₁₁, h11⟩ := eventually_le_rpow_neg localFlatLoss p11
  obtain ⟨d₁₂, hd₁₂, h12⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax) hν
  obtain ⟨d₁₃, hd₁₃, h13⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax) p13
  obtain ⟨d₁₄, hd₁₄, h14⟩ := eventually_le_rpow_neg quadLoss p14
  set δ₁ : ℝ := min (1 / 100) (min d₁ (min d₂ (min d₃ (min d₄ (min d₅ (min d₆ (min d₇
    (min d₈ (min d₉ (min d₁₀ (min d₁₁ (min d₁₂ (min d₁₃ d₁₄))))))))))))) with hδ₁def
  have hδ₁ : 0 < δ₁ := by
    simp only [hδ₁def, lt_min_iff]
    exact ⟨by norm_num, hd₁, hd₂, hd₃, hd₄, hd₅, hd₆, hd₇, hd₈, hd₉, hd₁₀, hd₁₁, hd₁₂, hd₁₃, hd₁₄⟩
  refine ⟨ζF, hζF, δ₁, hδ₁, ?_⟩
  intro δ hδ hδδ₁ L top hL hLlow hLup htopN htop1 htop2 m x v S a hmCp hprep hst
  simp only [hδ₁def, le_min_iff] at hδδ₁
  obtain ⟨h100, hδd₁, hδd₂, hδd₃, hδd₄, hδd₅, hδd₆, hδd₇, hδd₈, hδd₉, hδd₁₀, hδd₁₁, hδd₁₂,
    hδd₁₃, hδd₁₄⟩ := hδδ₁
  have hδ1 : δ ≤ 1 := h100.trans (by norm_num)
  have hinv : (1 / δ) ^ (ξ / 2) = δ ^ (-(ξ / 2)) := by
    rw [one_div, Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]
  refine sticky_branch_at_q (ξ := ξ) (ζ₂ := ζ₂) (ζ₃ := ζ₃) (ω := ω) (ν := ν) (ζF := ζF) (θ := θ)
    (e := e) (Nmax := Nmax) hξ hζ₂.le hζ₂ξ hν hζF.le hδ h100 (hdich δ hδ h100 hδd₁) hL hLup htopN
    htop1 htop2 x v S a hprep hst ?_ (h3 δ hδ hδd₃) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (h12 δ hδ hδd₁₂) ?_
  · -- the class-count bound of the flat exit
    intro n' hn'
    apply hpigE δ hδ hδd₂ n'
    have hm4 : (m : ℝ) ≤ Cp * δ ^ (-4 : ℝ) := by
      have h4pos : 0 < δ ^ (4 : ℝ) := Real.rpow_pos_of_pos hδ 4
      have hδ4 : δ ^ (4 : ℝ) = δ ^ 4 := by exact_mod_cast Real.rpow_natCast δ 4
      have hinv4 : δ ^ (-4 : ℝ) * δ ^ (4 : ℝ) = 1 := by rw [← Real.rpow_add hδ]; simp
      have : (m : ℝ) * δ ^ (4 : ℝ) ≤ Cp := by rw [hδ4]; exact hmCp
      calc (m : ℝ) = (m * δ ^ (4 : ℝ)) * δ ^ (-4 : ℝ) := by
            rw [mul_assoc, mul_comm (δ ^ (4 : ℝ)), hinv4, mul_one]
        _ ≤ Cp * δ ^ (-4 : ℝ) := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hδ.le _)
    have hn'm : (n' : ℝ) ≤ m := by exact_mod_cast hn'
    calc (n' : ℝ) ≤ m := hn'm
      _ ≤ Cp * δ ^ (-4 : ℝ) := hm4
      _ ≤ max Cp 1 * δ ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ.le _)
  · -- hbalc
    have := mul_rpow_neg_le_of_le (q := e) hδ (h4 δ hδ hδd₄)
    rwa [show ξ - e + e = ξ by ring] at this
  · -- hsmall
    have h := mul_rpow_le_one_of_le hδ (h5 δ hδ hδd₅)
    calc 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * (((Nmax : ℝ) + 1) * δ ^ e)
        = (2 * 2 ^ Nmax * N1) * (δ ^ (-(ν * Nmax)) * δ ^ e) := by rw [hN1def]; ring
      _ = (2 * 2 ^ Nmax * N1) * δ ^ (e - ν * Nmax) := by
          rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ 1 := h
  · -- hKM
    have h := mul_rpow_neg_le_of_le (q := ζF + ν * Nmax) hδ (h6 δ hδ hδd₆)
    calc 2 * δ ^ (-ζF) * (2 ^ Nmax * δ ^ (-(ν * Nmax)))
        = (2 * 2 ^ Nmax) * (δ ^ (-ζF) * δ ^ (-(ν * Nmax))) := by ring
      _ = (2 * 2 ^ Nmax) * δ ^ (-(ζF + ν * Nmax)) := by
          rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ δ ^ (-(ξ - ζF - ν * Nmax + (ζF + ν * Nmax))) := h
      _ = δ ^ (-ξ) := by congr 1; ring
  · -- hcρ
    have h := mul_rpow_neg_le_of_le (q := ζ₂ / 8 + ν + ζ₂ / 200 + ξ / 2 + ν) hδ
      (h7 δ hδ hδd₇)
    rw [hinv]
    calc 1600 * (122 ^ 3 * 16 ^ 3) * δ ^ (-(ζ₂ / 8)) * (16 * δ ^ (-ν - ζ₂ / 200)) *
          δ ^ (-(ξ / 2)) * δ ^ (-ν)
        = (1600 * (122 ^ 3 * 16 ^ 3) * 16) *
            (δ ^ (-(ζ₂ / 8)) * δ ^ (-ν - ζ₂ / 200) * δ ^ (-(ξ / 2)) * δ ^ (-ν)) := by ring
      _ = (1600 * (122 ^ 3 * 16 ^ 3) * 16) * δ ^ (-(ζ₂ / 8 + ν + ζ₂ / 200 + ξ / 2 + ν)) := by
          rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
          congr 2; ring
      _ ≤ δ ^ (-(ξ / 2 - ζ₂ / 8 - ζ₂ / 200 - e - 2 * ν +
            (ζ₂ / 8 + ν + ζ₂ / 200 + ξ / 2 + ν))) := h
      _ = δ ^ (-ξ) * δ ^ e := by
          rw [← Real.rpow_add hδ]; congr 1; ring
  · -- hcountKT
    have h := mul_rpow_le_one_of_le hδ (h8 δ hδ hδd₈)
    calc 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω
        = (2 * 2 ^ Nmax) * (δ ^ (-(ν * Nmax)) * δ ^ ω) := by ring
      _ = (2 * 2 ^ Nmax) * δ ^ (ω - ν * Nmax) := by
          rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ 1 := h
  · -- h64
    have h := mul_rpow_le_one_of_le hδ (h9 δ hδ hδd₉)
    exact h
  · -- hretain
    exact mul_rpow_le_one_of_le hδ (h10 δ hδ hδd₁₀)
  · -- herror
    exact mul_rpow_le_one_of_le hδ (h11 δ hδ hδd₁₁)
  · -- herrorQ
    exact mul_rpow_le_one_of_le hδ (h14 δ hδ hδd₁₄)
  · -- hcountF
    have h := mul_rpow_neg_le_of_le (q := -(ω - ν * Nmax)) hδ (h13 δ hδ hδd₁₃)
    calc 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω
        = (2 * 2 ^ Nmax) * (δ ^ (-(ν * Nmax)) * δ ^ ω) := by ring
      _ = (2 * 2 ^ Nmax) * δ ^ (-(-(ω - ν * Nmax))) := by
          rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ δ ^ (-(ω - θ - ν * Nmax + -(ω - ν * Nmax))) := h
      _ = δ ^ θ := by congr 1; ring

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
