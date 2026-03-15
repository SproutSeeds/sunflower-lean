import Mathlib

/-!
# Problem 151 scaffold

Source: https://www.erdosproblems.com/151

Statement:
For a graph $G$ let $\tau(G)$ denote the minimal number of vertices that include
at least one from each maximal clique of $G$ on at least two vertices
(sometimes called the clique transversal number). Let $H(n)$ be maximal such
that every triangle-free graph on $n$ vertices contains an independent set on
$H(n)$ vertices. If $G$ is a graph on $n$ vertices then is
\[\tau(G)\leq n-H(n)?\]

This file was bootstrapped by Ode To Erdos so the workspace can treat Problem
151 like the existing board-backed routes on first use.
-/

namespace SunflowerLean

/-- North-star scaffold for Erdős Problem 151. Replace `True` with the local formal statement. -/
def erdosProblem151NorthStar : Prop := True

/-- Initial route seed for Erdős Problem 151. Replace this with the first
meaningful local theorem lane. -/
theorem erdosProblem151RouteSeed : erdosProblem151NorthStar := by
  trivial

end SunflowerLean
