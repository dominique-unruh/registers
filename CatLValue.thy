theory CatLValue
  imports CatLValue_Axioms2
begin

definition 
  \<open>compatible x y \<longleftrightarrow> (\<forall>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f))\<close>

(* definition
  \<open>pair x y = (THE xy. \<forall>f g. xy \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g))\<close> *)

lemma pair_apply[simp]: 
  assumes "compatible x y"
  shows "pair x y \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g)"
  apply (rule pair_apply0) using assms by (simp add: compatible_def)

lemma compatibleI:
  assumes \<open>\<And>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f)\<close>
  shows "compatible x y"
  using assms unfolding compatible_def by simp

(* lemma compatibleI: 
  assumes "\<And>f g. pair x y \<cdot> (f \<otimes> g) = pair y x \<cdot> (g \<otimes> f)"
  shows "compatible x y"
  using assms unfolding compatible_def by simp *)

(* lemma compatibleI':
  assumes "pair x y = pair y x o\<^sub>l swap"
  shows "compatible x y"
  apply (rule compatibleI)
  by (simp add: assms) *)

definition "chain x y = x o\<^sub>l y"

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  by (simp add: compatible_def)

lemma lvalue_app_fun_cong: "f = g \<Longrightarrow> f \<cdot> x = g \<cdot> x" by simp

lemma compatible3:
  assumes [simp]: "compatible x y" and "compatible y z" and "compatible x z"
  shows "compatible (pair x y) z"
  apply (rule compatibleI)
  apply (rule compatible30)
  using assms unfolding compatible_def by auto
(* proof -
  have "pair (pair x y) z \<cdot> (f \<otimes> g) \<otimes> h = pair z (pair x y) \<cdot> h \<otimes> (f \<otimes> g)" for f g h
    apply auto using assms unfolding compatible_def
    by (metis maps_comp_assoc)k
  then have "(pair (pair x y) z o\<^sub>l swap o\<^sub>l left_tensor h) \<cdot> (f \<otimes> g)
           = (pair z (pair x y) o\<^sub>l left_tensor h) \<cdot> (f \<otimes> g)" for f g h
    by auto
  then have *: "(pair (pair x y) z o\<^sub>l swap o\<^sub>l left_tensor h)
           = (pair z (pair x y) o\<^sub>l left_tensor h)" for h
    by (rule tensor_extensionality)
  have "(pair (pair x y) z) \<cdot> (fg \<otimes> h)
           = (pair z (pair x y)) \<cdot> (h \<otimes> fg)" for fg h
    using *[THEN lvalue_app_fun_cong]
    by auto
  then show ?thesis
    unfolding compatible_def by simp
qed *)

lemma compatible_chain_left: "compatible x y \<Longrightarrow> compatible (chain x z) y"
  unfolding compatible_def chain_def lvalue_comp_app by auto
  
lemma compatible_chain_inner: 
  "compatible x y \<Longrightarrow> compatible (chain z x) (chain z y)"
  unfolding compatible_def chain_def  
  by (auto simp flip: lvalue_app_mult)

definition is_everything where
  "is_everything x \<longleftrightarrow> (\<exists>y. y o\<^sub>l x = 1\<^sub>l)"

(* definition is_everything2 where
  "is_everything2 x \<longleftrightarrow> inj (lvalue_app x)" *)

definition is_complement where
  "is_complement x y \<longleftrightarrow> compatible x y \<and> is_everything (pair x y)"

(* definition is_complement2 where
  "is_complement2 x y \<longleftrightarrow> compatible x y \<and> is_everything2 (pair x y)" *)

lemma tensor_extensionality3: 
  assumes "\<And>f g h. x \<cdot> (f \<otimes> g \<otimes> h) = y \<cdot> (f \<otimes> g \<otimes> h)"
  shows "x = y"
proof -
  from assms
  have "x o\<^sub>l left_tensor f \<cdot> (g \<otimes> h) = y o\<^sub>l left_tensor f \<cdot> (g \<otimes> h)" for f g h
    by auto
  then have "x o\<^sub>l left_tensor f = y o\<^sub>l left_tensor f" for f
    by (rule tensor_extensionality)
  then have "x \<cdot> (f \<otimes> gh) = y \<cdot> (f \<otimes> gh)" for f gh
    by (metis (no_types, lifting) left_tensor_apply lvalue_comp_app)
  then show ?thesis
    by (rule tensor_extensionality)
qed

lemma complement_chain:
  assumes "is_complement x x'"
  assumes "is_complement y y'"
  shows "is_complement (chain x y) (pair (chain x y') x')"
proof (simp add: is_complement_def, rule)
  have xx'[simp]: "compatible x x'" and yy'[simp]: "compatible y y'"
    and x'x[simp]: "compatible x' x" and y'y[simp]: "compatible y' y"
    using assms is_complement_def compatible_sym by blast+
  show compat: "compatible (chain x y) (pair (chain x y') x')"
    apply (rule compatible_sym)
    apply (rule compatible3)
      apply (rule compatible_chain_left, simp)
     apply (rule compatible_sym)
    apply (rule compatible_chain_left, simp)
    by (rule compatible_chain_inner, simp)
  from assms(1)
  obtain xInv where xInv: "xInv \<cdot> pair x x' \<cdot> f = f" for f
    unfolding is_complement_def is_everything_def
    by (metis lvalue_comp_app lvalue_id)
  from assms(2)
  obtain yInv where yInv: "yInv \<cdot> pair y y' \<cdot> f = f" for f
    unfolding is_complement_def is_everything_def
    by (metis lvalue_comp_app lvalue_id)

  define z where "z = assoc' o\<^sub>l lvalue_tensor yInv 1\<^sub>l o\<^sub>l xInv"
  have "z o\<^sub>l pair (chain x y) (pair (chain x y') x') \<cdot> (f \<otimes> (g \<otimes> h)) = (f \<otimes> (g \<otimes> h))" for f g h
  proof -
    have "pair (chain x y) (pair (chain x y') x') \<cdot> (f \<otimes> (g \<otimes> h))
      = (x \<cdot> y \<cdot> f) o\<^sub>m (x \<cdot> y' \<cdot> g) o\<^sub>m (x' \<cdot> h)"
      apply (subst pair_apply, rule compat)
      apply (subst pair_apply, simp add: compatible_chain_left)
      by (simp add: maps_comp_assoc chain_def)
    also have "\<dots> = (x \<cdot> (pair y y') \<cdot> (f \<otimes> g)) o\<^sub>m (x' \<cdot> h)"
      by (simp add: lvalue_app_mult)
    also have "\<dots> = (pair x x') \<cdot> ((pair y y' \<cdot> (f \<otimes> g)) \<otimes> h)"
      by simp
    also have "xInv \<cdot> ... = ((pair y y' \<cdot> (f \<otimes> g)) \<otimes> h)"
      using xInv apply simp by (metis pair_apply[OF xx'])
    also have "lvalue_tensor yInv 1\<^sub>l \<cdot> \<dots> = (f \<otimes> g) \<otimes> h"
      using yInv apply simp by (metis pair_apply[OF yy'])
    also have "assoc' \<cdot> \<dots> = f \<otimes> (g \<otimes> h)"
      by simp
    finally show ?thesis
      unfolding z_def by simp
  qed

  then have "z o\<^sub>l pair (chain x y) (pair (chain x y') x') = 1\<^sub>l"
    by (rule_tac tensor_extensionality3, simp)
  then show "is_everything (pair (chain x y) (pair (chain x y') x'))"
    unfolding is_everything_def by auto
qed

end
