theory AxiomsAdj_Quantum
  imports Axioms_Quantum
begin

definition sandwich where "sandwich a b = a o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L a*"

lemma lvalue_sandwhich_axiom:
  fixes a
  defines "A \<equiv> sandwich a"
  assumes \<open>unitary a\<close>
  assumes \<open>clinear A\<close>
  assumes \<open>A idOp = idOp\<close>
  assumes \<open>\<And>x y. A (x o\<^sub>C\<^sub>L y) = A x o\<^sub>C\<^sub>L A y\<close>
  assumes \<open>\<And>x. A (x*) = (A x)*\<close>
  shows \<open>lvalue A\<close>
  using assms by (auto simp: lvalue_def)


end
