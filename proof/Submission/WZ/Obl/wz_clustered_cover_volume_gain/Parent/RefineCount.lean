-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.RefineCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RefineStep
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.LocalScale

/-!
# A sub-collection of the `ρ`-cover carrying a fixed share of the mass is not small

With cover data `C` at error `δ^-h` (fibre sizes `δ^-h`-balanced) and a `δ^h`-dense input family,
the fibres over `U ⊆ Fin N` carrying a `δ^{h'}` share of the mass force
`δ^{h' + 3h} N ≤ 384 #U`: each fibre has at most `δ^-h n / N` tubes of volume `≤ 384 δ²`.
Combined with `refined_of_subcover` this is WZ §9, Step 1 (`refined_of_mass`).
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory

namespace Interfaces

theorem ncard_fibre_eq {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (k : Fin N) :
    Set.ncard {i | i ∈ S ∧ f i = k} = (S.filter fun i => f i = k).card := by
  classical
  rw [← Set.ncard_coe_finset, Finset.coe_filter]

theorem count_of_mass {δ h h' ρ : ℝ} {n N : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {S : Finset (Fin n)} {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (U : Finset (Fin N))
    (hmassU : o (δ ^ h') * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), μ (Z i)) :
    δ ^ (h' + 3 * h) * N ≤ 384 * U.card := by
  classical
  obtain ⟨hn, hadm, -, hdens, -, -⟩ := hA
  obtain ⟨hZ, hmass, -, -, -, -, hbal, -, -⟩ := hC
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hδh : 0 < δ ^ h := Real.rpow_pos_of_pos hδ h
  have hδ2 : 0 < δ ^ 2 := by positivity
  set fib : Fin N → ℕ := fun k => (S.filter fun i => f i = k).card with hfibdef
  have hbal' : ∀ k k', (fib k : ℝ) ≤ δ ^ (-h) * fib k' := by
    intro k k'
    have := hbal k k'
    simp only [q, ncard_fibre_eq] at this
    exact this
  have hsumfib : (∑ k, (fib k : ℝ)) = S.card := by
    have := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := Finset.univ)
      (fun i _ => Finset.mem_coe.mpr (Finset.mem_univ (f i)))
    rw [this]
    push_cast
    rfl
  have hScard : (S.card : ℝ) ≤ n := by
    have := Finset.card_le_univ S
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hfib_le : ∀ k, (N : ℝ) * fib k ≤ δ ^ (-h) * n := by
    intro k
    calc (N : ℝ) * fib k = ∑ _k' : Fin N, (fib k : ℝ) := by simp
      _ ≤ ∑ k', δ ^ (-h) * (fib k' : ℝ) := Finset.sum_le_sum fun k' _ => hbal' k k'
      _ = δ ^ (-h) * S.card := by rw [← Finset.mul_sum, hsumfib]
      _ ≤ δ ^ (-h) * n := by gcongr
  -- the number of tubes over `U`
  set SU := S.filter fun i => f i ∈ U with hSU
  have hSUcard : (SU.card : ℝ) = ∑ k ∈ U, (fib k : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := f) (s := SU) (t := U)
      (fun i hi => Finset.mem_coe.mpr (Finset.mem_filter.mp hi).2)
    rw [this]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    have hfe : SU.filter (fun i => f i = k) = S.filter (fun i => f i = k) := by
      ext i
      simp only [hSU, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hiS, _⟩, hik⟩; exact ⟨hiS, hik⟩
      · rintro ⟨hiS, hik⟩; exact ⟨⟨hiS, hik ▸ hk⟩, hik⟩
    rw [hfe]
  have hNSU : (N : ℝ) * SU.card ≤ U.card * (δ ^ (-h) * n) := by
    rw [hSUcard, Finset.mul_sum]
    calc ∑ k ∈ U, (N : ℝ) * fib k ≤ ∑ _k ∈ U, δ ^ (-h) * (n : ℝ) :=
          Finset.sum_le_sum fun k _ => hfib_le k
      _ = U.card * (δ ^ (-h) * n) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the mass over `U` is at most `384 δ² #SU`
  have hmass_up : ∑ i ∈ SU, μ (Z i) ≤ o (SU.card * (384 * δ ^ 2)) := by
    calc ∑ i ∈ SU, μ (Z i) ≤ ∑ _i ∈ SU, o (384 * δ ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          obtain ⟨hv, -, -, hYT⟩ := hadm i
          exact (measure_mono ((hZ i).2.1.trans hYT)).trans
            (tube_volume_upper hδ hδ1 (x i) (v i) hv)
      _ = o (SU.card * (384 * δ ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp only [o]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  -- the mass over `U` is at least `δ^{h'+2h} n δ²`
  have hmass_low : o (δ ^ h' * (δ ^ h * (δ ^ h * n * δ ^ 2))) ≤ ∑ i ∈ SU, μ (Z i) := by
    refine le_trans ?_ hmassU
    simp only [o] at hdens hmass ⊢
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
    calc ENNReal.ofReal (δ ^ h) * ENNReal.ofReal (δ ^ h * n * δ ^ 2)
        ≤ ENNReal.ofReal (δ ^ h) * ∑ i, μ (Y i) := by gcongr
      _ ≤ ∑ i ∈ S, μ (Z i) := hmass
  have hreal : δ ^ h' * (δ ^ h * (δ ^ h * n * δ ^ 2)) ≤ SU.card * (384 * δ ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hmass_low.trans hmass_up)
  -- combine
  have hrp : δ ^ (h' + 3 * h) = δ ^ h' * δ ^ h * δ ^ h * δ ^ h := by
    rw [show h' + 3 * h = h' + h + h + h by ring, Real.rpow_add hδ, Real.rpow_add hδ,
      Real.rpow_add hδ]
  have hneg : δ ^ h * δ ^ (-h) = 1 := by
    rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
  have h1 : δ ^ h' * δ ^ h * δ ^ h * n ≤ 384 * SU.card := by
    have := hreal
    have h2 : δ ^ h' * (δ ^ h * (δ ^ h * n * δ ^ 2)) = (δ ^ h' * δ ^ h * δ ^ h * n) * δ ^ 2 := by
      ring
    rw [h2] at this
    nlinarith
  have h3 : δ ^ (h' + 3 * h) * N * n ≤ 384 * U.card * n := by
    rw [hrp]
    calc δ ^ h' * δ ^ h * δ ^ h * δ ^ h * N * n
        = δ ^ h * N * (δ ^ h' * δ ^ h * δ ^ h * n) := by ring
      _ ≤ δ ^ h * N * (384 * SU.card) := by gcongr
      _ = 384 * δ ^ h * (N * SU.card) := by ring
      _ ≤ 384 * δ ^ h * (U.card * (δ ^ (-h) * n)) := by gcongr
      _ = 384 * U.card * n * (δ ^ h * δ ^ (-h)) := by ring
      _ = 384 * U.card * n := by rw [hneg, mul_one]
  exact le_of_mul_le_mul_right h3 hnpos

/-- **WZ §9, Step 1.** A sub-collection of the `ρ`-tubes whose fibres carry a `δ^{h'}` share of
the mass and which obeys the Katz–Tao count with error `δ^-ζ` gives o019's alternative (B),
provided `h + h' ≤ ζ` and `δ` is small (`384 δ^{ζ - h' - 4h} ≤ 1`). -/
theorem refined_of_mass {ζ δ h h' ρ : ℝ} {n N : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {S : Finset (Fin n)} {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh' : 0 ≤ h') (hζ : h + h' ≤ ζ)
    (hsmall : 384 * δ ^ (ζ - h' - 4 * h) ≤ 1)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (U : Finset (Fin N))
    (hmassU : o (δ ^ h') * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), μ (Z i))
    (hKU : ∀ W, Convex ℝ W →
      o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o (δ ^ (-ζ)) * μ W) :
    Refined ζ δ ρ n x v Y S Z := by
  classical
  have hcount := count_of_mass hδ hδ1 hA hC U hmassU
  have hn : (0 : ℝ) < n := by exact_mod_cast hA.1
  -- the mass condition of the refinement
  have hmass : o (δ ^ ζ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), μ (Z i) := by
    refine le_trans ?_ hmassU
    have hC2 := hC.2.1
    have hle : δ ^ ζ ≤ δ ^ h' * δ ^ h := by
      rw [← Real.rpow_add hδ]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc o (δ ^ ζ) * ∑ i, μ (Y i) ≤ o (δ ^ h' * δ ^ h) * ∑ i, μ (Y i) := by
          gcongr; exact ENNReal.ofReal_le_ofReal hle
      _ = o (δ ^ h') * (o (δ ^ h) * ∑ i, μ (Y i)) := by
          simp only [o]
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ o (δ ^ h') * ∑ i ∈ S, μ (Z i) := by gcongr
  -- `U` is nonempty: the total mass is positive
  have hUne : U.Nonempty := by
    by_contra hU
    rw [Finset.not_nonempty_iff_eq_empty] at hU
    subst hU
    have h0 : ∑ i ∈ S.filter (fun i => f i ∈ (∅ : Finset (Fin N))), μ (Z i) = 0 := by simp
    rw [h0] at hmass
    have hpos : 0 < o (δ ^ ζ) * ∑ i, μ (Y i) := by
      apply ENNReal.mul_pos
      · simp only [o]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      · have := (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < δ ^ h * n * δ ^ 2)).trans_le
          hA.2.2.2.1
        exact this.ne'
    exact absurd (hpos.trans_le hmass) (lt_irrefl 0)
  -- `U` is not too small
  have hN : δ ^ (-h) * N ≤ δ ^ (-ζ) * U.card := by
    have hδpow : δ ^ (-h) = δ ^ (h' + 3 * h) * δ ^ (-(h' + 4 * h)) := by
      rw [← Real.rpow_add hδ]; ring_nf
    have hζpow : δ ^ (-(h' + 4 * h)) * 384 ≤ δ ^ (-ζ) := by
      have : δ ^ (-ζ) = δ ^ (-(h' + 4 * h)) * δ ^ (-(ζ - h' - 4 * h)) := by
        rw [← Real.rpow_add hδ]; ring_nf
      rw [this]
      gcongr
      rw [Real.rpow_neg hδ.le]
      rw [le_inv_comm₀ (by norm_num) (by positivity)]
      rw [inv_eq_one_div, le_div_iff₀ (by norm_num)]
      linarith
    calc δ ^ (-h) * N = δ ^ (-(h' + 4 * h)) * (δ ^ (h' + 3 * h) * N) := by rw [hδpow]; ring
      _ ≤ δ ^ (-(h' + 4 * h)) * (384 * U.card) := by gcongr
      _ = δ ^ (-(h' + 4 * h)) * 384 * U.card := by ring
      _ ≤ δ ^ (-ζ) * U.card := by gcongr
  have hhζ : h ≤ ζ := by linarith
  exact refined_of_subcover hδ hδ1 hhζ hC U hUne hmass hKU hN

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
