section \<open>Using the axioms\<close>

theory CatLValue
  imports CatLValue_Axioms1
begin

definition 
  \<open>compatible x y \<longleftrightarrow> (is_lvalue x \<and> is_lvalue y \<and> (\<forall>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f)))\<close>

(* definition
  \<open>pair x y = (THE xy. \<forall>f g. xy \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g))\<close> *)

(* lemma pair_apply[simp]:
  assumes "compatible x y"
  shows "pair x y \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g)"
  apply (rule pair_apply0) using assms by (simp add: compatible_def) *)

declare pair_apply[simp]
declare lvalue_id[simp]
declare lvalue_comp_app[simp]
(* declare lvalue_tensor_app[simp] *)
declare left_tensor_apply[simp]
declare swap_apply[simp]
declare assoc_apply[simp]
declare assoc'_apply[simp]

lemma compatibleI:
  assumes "is_lvalue x" and "is_lvalue y"
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
proof (rule compatibleI)
  have "pair (pair x y) z \<cdot> (f \<otimes> g) \<otimes> h = pair z (pair x y) \<cdot> h \<otimes> (f \<otimes> g)" for f g h
    apply auto using assms unfolding compatible_def
    by (metis maps_comp_assoc)
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
  then show "(pair x y \<cdot> fg) o\<^sub>m (z \<cdot> h) = (z \<cdot> h) o\<^sub>m (pair x y \<cdot> fg)" for fg h
    unfolding compatible_def by simp
  show "is_lvalue z"
    using assms(2) compatible_def by auto
  show "is_lvalue (pair x y)" 
    by (meson assms(1) compatible_def pair_is_lvalue0)
qed

lemma compatible_chain_left: "compatible x y \<Longrightarrow> is_lvalue z \<Longrightarrow> compatible (chain x z) y"
  by (auto simp: chain_def comp_is_lvalue compatible_def)
  
lemma compatible_chain_inner: 
  "compatible x y \<Longrightarrow> is_lvalue z \<Longrightarrow> compatible (chain z x) (chain z y)"
  by (auto simp flip: lvalue_app_mult simp: compatible_def chain_def comp_is_lvalue)

definition is_everything where
  "is_everything x \<longleftrightarrow> (\<exists>y. y o\<^sub>l x = 1\<^sub>l)"

(* definition is_everything where
  "is_everything x \<longleftrightarrow> inj (lvalue_app x)" *)

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

(* TODO: Can we do this without lvalue_tensor? *)
lemma complement_chain:
  assumes "is_complement x x'"
  assumes "is_complement y y'"
  shows "is_complement (chain x y) (pair (chain x y') x')"
proof (simp add: is_complement_def, rule)
  have xx'[simp]: "compatible x x'" and yy'[simp]: "compatible y y'"
    and x'x[simp]: "compatible x' x" and y'y[simp]: "compatible y' y"
    using assms is_complement_def compatible_sym by blast+
  then have [simp]: "is_lvalue x" "is_lvalue x'" "is_lvalue y" "is_lvalue y'"
    using compatible_def by blast+
  show compat: "compatible (chain x y) (pair (chain x y') x')"
    apply (rule compatible_sym)
    apply (rule compatible3)
      apply (rule compatible_chain_left, simp, simp)
     apply (rule compatible_sym)
    apply (rule compatible_chain_left, simp, simp)
    by (rule compatible_chain_inner, simp_all)
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
      by (simp add: maps_comp_assoc chain_def)
    moreover have "\<dots> = (x \<cdot> (pair y y') \<cdot> (f \<otimes> g)) o\<^sub>m (x' \<cdot> h)"
      by (simp add: lvalue_app_mult)
    moreover have "\<dots> = (pair x x') \<cdot> ((pair y y' \<cdot> (f \<otimes> g)) \<otimes> h)"
      by simp
    moreover have "xInv \<cdot> ... = ((pair y y' \<cdot> (f \<otimes> g)) \<otimes> h)"
      using xInv apply simp by (metis pair_apply)
    moreover have "lvalue_tensor yInv 1\<^sub>l \<cdot> \<dots> = (f \<otimes> g) \<otimes> h"
      using yInv apply simp
      by (metis lvalue_id lvalue_tensor_app pair_apply yInv)
    moreover have "assoc' \<cdot> \<dots> = f \<otimes> (g \<otimes> h)"
      by simp
    ultimately show ?thesis
      unfolding z_def by simp
  qed

  then have "z o\<^sub>l pair (chain x y) (pair (chain x y') x') = 1\<^sub>l"
    by (rule_tac tensor_extensionality3, simp)
  then show "is_everything (pair (chain x y) (pair (chain x y') x'))"
    unfolding is_everything_def by auto
qed

end
