/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/RowOptions.lean.
   Earlier provenance comments in the source are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.RowCounting

/-!
# Row options at one horizontal cell

Rows `T n` of deep labels `n` predict a per-incidence value `y` (the zoomed
transverse velocity) at the incidence's velocity `v`, to `e₁`.  The value `y`
lies, at width `E₁`, in a short list `L (c, w)` depending only on the
horizontal cell `c` and the velocity bin `w = ⌊v / ξ⌋`.  If every deep label
counted at the cell `c` has witnesses in a set of velocity bins of palette
weight at least `θ`, then the rows at `c` occupy few bins of width `E`.

This is the counting step of the paper's verification of the row-fit
hypotheses (Proposition 8.5): two separated witness velocities pin a row by
interpolation, and the palette product weight of the witness pairs pays for
the options.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.RowOptions

open Submission.Obl.k4_narrow_projected_row_parents.RowCounting

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Integer bin of a row. -/
def rowBin (E : ℝ) (T : Fin 2 → ℝ) : Fin 2 → ℤ := fun i => ⌊T i / E⌋

theorem abs_sub_rowBin {E x : ℝ} (hE : 0 < E) : |x - E * ⌊x / E⌋| ≤ E := by
  have h1 := Int.floor_le (x / E)
  have h2 := Int.lt_floor_add_one (x / E)
  have h1' : E * ⌊x / E⌋ ≤ x := by
    have := mul_le_mul_of_nonneg_left h1 hE.le
    rwa [mul_div_cancel₀ _ hE.ne'] at this
  have h2' : x < E * ⌊x / E⌋ + E := by
    have := mul_lt_mul_of_pos_left h2 hE
    rw [mul_div_cancel₀ _ hE.ne', mul_add, mul_one] at this
    exact this
  rw [abs_le]; constructor <;> linarith

/-- **Row options at one cell.**  `S` is the finite set of deep labels counted
at the cell; each has witness bins `V n` of palette weight at least `θ`, and at
each witness bin an incidence whose value is in the list.  -/
theorem row_options_card {Z : Type*} (T : ℕ → Fin 2 → ℝ) (L : ℤ → Finset ℤ) (π' : ℤ → ℝ)
    (vel yv : Z → ℝ) (lab : Z → ℕ) (vb : Z → ℤ)
    {ξ E E₁ e₁ Kt Kc θ : ℝ} (hξ : 0 < ξ) (hE : 0 < E) (hE₁ : 0 < E₁)
    (he₁ : 0 ≤ e₁) (hKt : 0 ≤ Kt) (hKc : 1 ≤ Kc) (hθ : 0 < θ)
    (bins : Finset ℤ) (S : Finset ℕ) (V : ℕ → Finset ℤ)
    (hπ0 : ∀ w, 0 ≤ π' w) (hπsum : ∑ w ∈ bins, π' w ≤ 1)
    (hbins : ∀ w ∈ bins, |(w : ℝ) * ξ| ≤ Kc)
    (hLcard : ∀ w ∈ bins, ((L w).card : ℝ) ≤ Kc)
    (hVsub : ∀ n ∈ S, V n ⊆ bins)
    (hVw : ∀ n ∈ S, θ ≤ ∑ w ∈ V n, π' w)
    (hthin : ∀ w₀ ∈ bins, ∑ w ∈ bins.filter (fun w : ℤ => |(w : ℝ) * ξ - (w₀ : ℝ) * ξ| < 1 / Kc),
      π' w ≤ θ / 2)
    (hwit : ∀ n ∈ S, ∀ w ∈ V n, ∃ z, lab z = n ∧ vb z = w ∧
      |vel z - (w : ℝ) * ξ| ≤ ξ ∧ |T n 1| ≤ Kt ∧ |T n 0 + vel z * T n 1 - yv z| ≤ e₁ ∧
        ⌊yv z / E₁⌋ ∈ L w) :
    ((S.image fun n => rowBin E (T n)).card : ℝ) ≤
      Kc ^ 2 * (12 * Kc ^ 2 * (2 + Kc + Kt * ξ / E + e₁ / E + E₁ / E) + 2) ^ 2 /
        (θ ^ 2 / 2) := by
  classical
  set rows := S.image fun n => rowBin E (T n)
  let vel' : Finset ℝ := bins.image fun w : ℤ => (w : ℝ) * ξ
  -- velocity representatives determine their bins
  have hinj : ∀ w w' : ℤ, (w : ℝ) * ξ = (w' : ℝ) * ξ → w = w' := by
    intro w w' h
    have := mul_right_cancel₀ hξ.ne' h
    exact_mod_cast this
  let bin : ℝ → ℤ := fun v => ⌊v / ξ⌋
  have hbin : ∀ w : ℤ, bin ((w : ℝ) * ξ) = w := by
    intro w; simp only [bin]; rw [mul_div_cancel_right₀ _ hξ.ne']; simp
  let weight : ℝ → ℝ := fun v => π' (bin v)
  let good : (Fin 2 → ℤ) → ℝ → Prop := fun r v =>
    ∃ n ∈ S, rowBin E (T n) = r ∧ bin v ∈ V n
  let sc : ℤ → ℝ := fun y => (y : ℝ) * E₁ / E
  let L' : ℝ → Finset ℝ := fun v => Finset.image sc (L (bin v))
  set Dt := 2 + Kc + Kt * ξ / E + e₁ / E + E₁ / E with hDt
  have hDt0 : 0 ≤ Dt := by positivity
  -- sums over the representatives are sums over the bins
  have hsumimg : ∀ f : ℝ → ℝ, ∑ v ∈ vel', f v = ∑ w ∈ bins, f ((w : ℝ) * ξ) := by
    intro f
    exact Finset.sum_image (fun w _ w' _ h => hinj w w' h)
  have hweight : ∀ w : ℤ, weight ((w : ℝ) * ξ) = π' w := fun w => by simp only [weight, hbin]
  have hmain := row_list_card_from_palette_pairs rows vel' weight good L' (K := Kc) (D := Dt)
    (m := θ ^ 2 / 2) hKc hDt0 (by positivity)
    (by
      intro v hv
      obtain ⟨w, -, hwv⟩ := Finset.mem_image.mp hv
      rw [← hwv, hweight]; exact hπ0 w)
    (by rw [hsumimg]; simp only [hweight]; exact hπsum)
    (by
      intro v hv
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
      rw [← hwv]; exact hbins w hw)
    (by
      intro v hv
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
      rw [← hwv]
      have hc : (L' ((w : ℝ) * ξ)).card ≤ (L w).card := by
        show (Finset.image sc (L (bin ((w : ℝ) * ξ)))).card ≤ (L w).card
        rw [hbin]; exact Finset.card_image_le
      exact le_trans (Nat.cast_le.mpr hc) (hLcard w hw))
    (by
      intro r hr v hv hgood
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
      subst hwv
      obtain ⟨n, hn, hrn, hwV⟩ := hgood
      rw [hbin] at hwV
      obtain ⟨z, -, -, hvz, hT1, hpz, hyz⟩ := hwit n hn w hwV
      refine ⟨(⌊yv z / E₁⌋ : ℝ) * E₁ / E, ?_, ?_⟩
      · show (⌊yv z / E₁⌋ : ℝ) * E₁ / E ∈ Finset.image sc (L (bin ((w : ℝ) * ξ)))
        rw [hbin]
        exact Finset.mem_image.mpr ⟨_, hyz, rfl⟩
      · rw [← hrn]
        simp only [rowBin]
        have h0 := abs_sub_rowBin (x := T n 0) hE
        have h1 := abs_sub_rowBin (x := T n 1) hE
        have hy := abs_sub_rowBin (x := yv z) hE₁
        have hwK : |(w : ℝ) * ξ| ≤ Kc := hbins w hw
        -- multiply through by E
        rw [show ((⌊T n 0 / E⌋ : ℤ) : ℝ) + (w : ℝ) * ξ * ((⌊T n 1 / E⌋ : ℤ) : ℝ) -
            (⌊yv z / E₁⌋ : ℝ) * E₁ / E =
          ((E * ⌊T n 0 / E⌋ - T n 0) + (w : ℝ) * ξ * (E * ⌊T n 1 / E⌋ - T n 1) +
            ((w : ℝ) * ξ - vel z) * T n 1 + (T n 0 + vel z * T n 1 - yv z) +
            (yv z - E₁ * ⌊yv z / E₁⌋)) / E by field_simp; ring]
        rw [abs_div, abs_of_pos hE, div_le_iff₀ hE]
        have e1 : |(w : ℝ) * ξ * (E * ⌊T n 1 / E⌋ - T n 1)| ≤ Kc * E := by
          rw [abs_mul]
          exact mul_le_mul hwK (by rw [abs_sub_comm]; exact h1) (abs_nonneg _) (by linarith)
        have e2 : |((w : ℝ) * ξ - vel z) * T n 1| ≤ ξ * Kt := by
          rw [abs_mul]
          exact mul_le_mul (by rw [abs_sub_comm]; exact hvz) hT1 (abs_nonneg _) hξ.le
        have e0 : |E * ⌊T n 0 / E⌋ - T n 0| ≤ E := by rw [abs_sub_comm]; exact h0
        have hsum5 := abs_add_le ((E * ⌊T n 0 / E⌋ - T n 0) + (w : ℝ) * ξ * (E * ⌊T n 1 / E⌋ - T n 1) +
            ((w : ℝ) * ξ - vel z) * T n 1 + (T n 0 + vel z * T n 1 - yv z))
            (yv z - E₁ * ⌊yv z / E₁⌋)
        have hsum4 := abs_add_le ((E * ⌊T n 0 / E⌋ - T n 0) + (w : ℝ) * ξ * (E * ⌊T n 1 / E⌋ - T n 1) +
            ((w : ℝ) * ξ - vel z) * T n 1) (T n 0 + vel z * T n 1 - yv z)
        have hsum3 := abs_add_le ((E * ⌊T n 0 / E⌋ - T n 0) + (w : ℝ) * ξ * (E * ⌊T n 1 / E⌋ - T n 1))
            (((w : ℝ) * ξ - vel z) * T n 1)
        have hsum2 := abs_add_le (E * ⌊T n 0 / E⌋ - T n 0) ((w : ℝ) * ξ * (E * ⌊T n 1 / E⌋ - T n 1))
        have hDtE : Dt * E = 2 * E + Kc * E + Kt * ξ + e₁ + E₁ := by
          rw [hDt, add_mul, add_mul, add_mul, add_mul, div_mul_cancel₀ _ hE.ne',
            div_mul_cancel₀ _ hE.ne', div_mul_cancel₀ _ hE.ne']
        rw [hDtE]
        linarith)
    (by
      intro r hr
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
      have hVb := hVsub n hn
      suffices key : θ ^ 2 / 2 ≤ ∑ w ∈ bins, ∑ w' ∈ bins, π' w * π' w' *
          (if 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ| ∧ good (rowBin E (T n)) ((w : ℝ) * ξ) ∧
            good (rowBin E (T n)) ((w' : ℝ) * ξ) then (1 : ℝ) else 0) by
        refine key.trans (le_of_eq ?_)
        rw [hsumimg]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hsumimg]
        refine Finset.sum_congr rfl fun w' _ => ?_
        rw [hweight, hweight]
        congr 1
        split_ifs <;> rfl
      -- lower bound by the witness bins
      have hgoodV : ∀ w ∈ V n, good (rowBin E (T n)) ((w : ℝ) * ξ) :=
        fun w hw => ⟨n, hn, rfl, by rw [hbin]; exact hw⟩
      have hθV := hVw n hn
      set θ' := ∑ w ∈ V n, π' w with hθ'
      have hinner : ∀ w ∈ V n, π' w * (θ' - θ / 2) ≤ ∑ w' ∈ bins, π' w * π' w' *
          (if 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ| ∧ good (rowBin E (T n)) ((w : ℝ) * ξ) ∧
            good (rowBin E (T n)) ((w' : ℝ) * ξ) then (1 : ℝ) else 0) := by
        intro w hw
        have hwb := hVb hw
        have hfar : θ' - θ / 2 ≤ ∑ w' ∈ (V n).filter
            (fun w' : ℤ => 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ|), π' w' := by
          have hsplit := Finset.sum_filter_add_sum_filter_not (V n)
            (fun w' : ℤ => 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ|) π'
          have hnear : ∑ w' ∈ (V n).filter
              (fun w' : ℤ => ¬ 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ|), π' w' ≤ θ / 2 := by
            refine le_trans ?_ (hthin w hwb)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro w' hw'
              simp only [Finset.mem_filter, not_le] at hw' ⊢
              exact ⟨hVb hw'.1, hw'.2⟩
            · intro w' _ _; exact hπ0 w'
          linarith
        calc π' w * (θ' - θ / 2) ≤ π' w * ∑ w' ∈ (V n).filter
              (fun w' : ℤ => 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ|), π' w' :=
              mul_le_mul_of_nonneg_left hfar (hπ0 w)
          _ = ∑ w' ∈ (V n).filter (fun w' : ℤ => 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ|),
                π' w * π' w' * (if 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ| ∧
                  good (rowBin E (T n)) ((w : ℝ) * ξ) ∧
                  good (rowBin E (T n)) ((w' : ℝ) * ξ) then (1 : ℝ) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro w' hw'
              obtain ⟨hw'V, hw'far⟩ := Finset.mem_filter.mp hw'
              rw [if_pos ⟨hw'far, hgoodV w hw, hgoodV w' hw'V⟩, mul_one]
          _ ≤ _ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro w' hw'
                exact hVb (Finset.mem_filter.mp hw').1
              · intro w' _ _
                apply mul_nonneg (mul_nonneg (hπ0 w) (hπ0 w'))
                split_ifs <;> norm_num
      calc θ ^ 2 / 2 ≤ θ' * (θ' - θ / 2) := by nlinarith
        _ = ∑ w ∈ V n, π' w * (θ' - θ / 2) := by rw [hθ', Finset.sum_mul]
        _ ≤ ∑ w ∈ V n, ∑ w' ∈ bins, π' w * π' w' *
              (if 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ| ∧ good (rowBin E (T n)) ((w : ℝ) * ξ) ∧
                good (rowBin E (T n)) ((w' : ℝ) * ξ) then (1 : ℝ) else 0) :=
            Finset.sum_le_sum hinner
        _ ≤ ∑ w ∈ bins, ∑ w' ∈ bins, π' w * π' w' *
              (if 1 / Kc ≤ |(w' : ℝ) * ξ - (w : ℝ) * ξ| ∧ good (rowBin E (T n)) ((w : ℝ) * ξ) ∧
                good (rowBin E (T n)) ((w' : ℝ) * ξ) then (1 : ℝ) else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hVb
            intro w _ _
            apply Finset.sum_nonneg
            intro w' _
            apply mul_nonneg (mul_nonneg (hπ0 w) (hπ0 w'))
            split_ifs <;> norm_num)
  exact hmain

end

end Submission.Obl.k4_narrow_projected_row_parents.RowOptions
