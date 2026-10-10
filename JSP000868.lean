/-
JSP-000868: radius-two bound for connected polynomial lemniscates.

Target theorem: a monic nonconstant complex polynomial whose closed unit
lemniscate {z | ‖f.eval z‖ ≤ 1} is connected has that lemniscate contained in a
closed disk of radius 2 (centered at the root centroid).

Proof strategy (Pommerenke's Jensen argument):
- `JSP000868.JensenWeight`: the one-dimensional estimate — if x₁,…,xₙ ∈ [A,B]
  and ∏ᵢ |y − xᵢ| ≤ 1 for all y ∈ [A,B], then B − (mean of xᵢ) ≤ 2.
- `JSP000868.Main`: project the connected lemniscate onto an arbitrary unit
  direction; connectedness makes the projection an interval; the projected roots
  satisfy the 1D hypothesis; the 1D estimate bounds every directional projection
  of (z − centroid) by 2, hence ‖z − centroid‖ ≤ 2.
-/
import JSP000868.JensenWeight
import JSP000868.Main
