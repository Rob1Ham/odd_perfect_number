module

public import OddPerfect.TothCandidates

public section

namespace OddPerfect.Toth

/-- Divide a long finite interval into adjacent pieces. Evaluation at a
leaf visits only its own points, keeping the kernel's recursion shallow. -/
@[expose] def pointRange (D S : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, a, w => decide (∀ j : Fin w, checkPoint (D*(a+j.val)) (S*((a+j.val)^2+(a+j.val)+1)))
  | fuel+1, a, w =>
    let k := w/2
    pointRange D S fuel a k && pointRange D S fuel (a+k) (w-k)

theorem pointRange_sound {D S fuel a w : ℕ} (h : pointRange D S fuel a w) (j : Fin w) :
    checkPoint (D*(a+j.val)) (S*((a+j.val)^2+(a+j.val)+1)) := by
  induction fuel generalizing a w with
  | zero => exact of_decide_eq_true h j
  | succ f ih =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
    by_cases hj : j.val<w/2
    · exact ih hl ⟨j.val,hj⟩
    · have pos : j.val-w/2 < w-w/2 := by have := j.isLt; omega
      have hit := ih hr ⟨j.val-w/2,pos⟩
      have eq : a+w/2+(j.val-w/2)=a+j.val := by omega
      simpa only [eq] using hit

theorem closed_last_prime_range {B D S a : ℕ} (fuel : ℕ) (limit : B<D*a^2)
    (empty : checkPoint D S) (points : pointRange D S fuel a (B/D+1-a)) : Closed B D S a :=
  closed_last_prime limit empty (pointRange_sound points)

end OddPerfect.Toth
