theory Example_Sufficient
  imports Sufficient
begin

(* Example 18 *)

datatype states = q0 | q1 | q2 | q3

instantiation states :: finite
begin

instance
proof (standard)
  have "(UNIV :: states set) \<subseteq> {q0, q1, q2, q3}"
    using states.exhaust by blast
  then show "finite (UNIV :: states set)"
    using finite_subset by auto
qed

end

datatype Sigma = a | b

instantiation Sigma :: finite
begin

instance
proof (standard)
  have "(UNIV :: Sigma set) \<subseteq> {a, b}"
    using Sigma.exhaust by blast
  then show "finite (UNIV :: Sigma set)"
    using finite_subset by auto
qed

end

(* Figure 3a *)

inductive delta :: "states \<Rightarrow> Sigma \<Rightarrow> states \<times> Sigma list \<Rightarrow> bool" where
  "delta q0 a (q1, [a, b, a])"
| "delta q0 a (q2, [a, b, a, b])"
| "delta q0 a (q3, [a, b, a, b])"
| "delta q1 a (q0, [b, a])"
| "delta q1 a (q0, [b, a, b])"
| "delta q2 a (q0, [a, b])"
| "delta q3 b (q0, [a, a])"

lemma finite_delta: "finite {x. delta q z x}"
proof -
  have "{x. delta q z x} \<subseteq> UNIV \<times> {xs. length xs \<le> 4}"
    by (auto elim: delta.cases)
  then show ?thesis
    using finite_subset finite_bounded_lists by fastforce
qed

interpretation NFT q0 delta "\<lambda>q. q = q0" UNIV
  using finite_UNIV finite_delta
  by unfold_locales auto

lemma comp_q0_qf: "computation q0 ([a, b], [a, b, a, b, a, a]) q0"
  using comp_trans[OF one_step[OF delta.intros(3)] one_step[OF delta.intros(7)]]
  by auto

lemma comp_q1_dest: "computation q1 (zs, bs) q' \<Longrightarrow> (zs = [] \<and> bs = [] \<and> q' = q1) \<or>
  (\<exists>zs' bs'. computation q0 (zs', bs') q' \<and> zs = a # zs' \<and> bs = b # a # bs') \<or>
  (\<exists>zs' bs'. computation q0 (zs', bs') q' \<and> zs = a # zs' \<and> bs = b # a # b # bs')"
  by (auto elim: computation.cases elim!: delta.cases)

lemma comp_q2_dest: "computation q2 (zs, bs) q' \<Longrightarrow> (zs = [] \<and> bs = [] \<and> q' = q2) \<or>
  (\<exists>zs' bs'. computation q0 (zs', bs') q' \<and> zs = a # zs' \<and> bs = a # b # bs')"
  by (auto elim: computation.cases elim!: delta.cases)

lemma comp_q3_dest: "computation q3 (zs, bs) q' \<Longrightarrow> (zs = [] \<and> bs = [] \<and> q' = q3) \<or>
  (\<exists>zs' bs'. computation q0 (zs', bs') q' \<and> zs = b # zs' \<and> bs = a # a # bs')"
  by (auto elim: computation.cases elim!: delta.cases)

lemma comp_q0_q0_dest: "computation q0 (zs, bs) q0 \<Longrightarrow> (zs = [] \<and> bs = []) \<or>
  (\<exists>zs' bs'. computation q0 (zs', bs') q0 \<and> zs = a # a # zs' \<and> bs = a # b # a # b # a # bs') \<or>
  (\<exists>zs' bs'. computation q0 (zs', bs') q0 \<and> zs = a # a # zs' \<and> bs = a # b # a # b # a # b # bs') \<or>
  (\<exists>zs' bs'. computation q0 (zs', bs') q0 \<and> zs = a # b # zs' \<and> bs = a # b # a # b # a # a # bs')"
  by (auto elim: computation.cases elim!: delta.cases dest!: comp_q1_dest comp_q2_dest comp_q3_dest)

definition "T = {([a, a], [a, b, a, b, a]), ([a, a], [a, b, a, b, a, b]),
  ([a, b], [a, b, a, b, a, a])}"

fun app_ls :: "'a list \<times> 'b list \<Rightarrow> 'a list \<times> 'b list \<Rightarrow> 'a list \<times> 'b list" where
  "app_ls (xs, ys) (xs', ys') = (xs @ xs', ys @ ys')"

context
  fixes T :: "(Sigma list \<times> Sigma list) set"
begin

inductive Tstar :: "Sigma list \<times> Sigma list \<Rightarrow> bool" where
  "Tstar ([], [])"
| "x \<in> T \<Longrightarrow> Tstar y \<Longrightarrow> Tstar (app_ls x y)"

end

lemma lang: "\<tau> = {x. Tstar T x}"
proof (rule set_eqI, rule iffI)
  fix x
  assume lassm: "x \<in> \<tau>"
  obtain as bs where x_def: "x = (as, bs)"
    by (cases x) auto
  have comp: "computation q0 (as, bs) q0"
    using lassm
    unfolding \<tau>_def x_def
    by auto
  then have "Tstar T x"
    unfolding x_def
  proof (induction "length as" arbitrary: as bs rule: nat_less_induct)
    case 1
    have IH: "\<And>as' bs'. length as' < length as \<Longrightarrow> computation q0 (as', bs') q0 \<Longrightarrow>
      Tstar T (as', bs')"
      using 1(1)
      by auto
    {
      fix as' bs'
      assume "computation q0 (as', bs') q0" "as = a # a # as'" "bs = a # b # a # b # a # bs'"
      then have "([a, a], [a, b, a, b, a]) \<in> T" "Tstar T (as', bs')"
        using IH
        by (auto simp: T_def)
      then have "Tstar T (a # a # as', a # b # a # b # a # bs')"
        using Tstar.intros(2)
        by fastforce
    }
    moreover
    {
      fix as' bs'
      assume "computation q0 (as', bs') q0" "as = a # a # as'" "bs = a # b # a # b # a # b # bs'"
      then have "([a, a], [a, b, a, b, a, b]) \<in> T" "Tstar T (as', bs')"
        using IH
        by (auto simp: T_def)
      then have "Tstar T (a # a # as', a # b # a # b # a # b # bs')"
        using Tstar.intros(2)
        by fastforce
    }
    moreover
    {
      fix as' bs'
      assume "computation q0 (as', bs') q0" "as = a # b # as'" "bs = a # b # a # b # a # a # bs'"
      then have "([a, b], [a, b, a, b, a, a]) \<in> T" "Tstar T (as', bs')"
        using IH
        by (auto simp: T_def)
      then have "Tstar T (a # b # as', a # b # a # b # a # a # bs')"
        using Tstar.intros(2)
        by fastforce
    }
    ultimately show ?case
      using comp_q0_q0_dest[OF 1(2)]
      by (auto intro: Tstar.intros)
  qed
  then show "x \<in> {x. Tstar T x}"
    by auto
next
  fix x
  assume "x \<in> {x. Tstar T x}"
  then have "Tstar T x"
    by auto
  then show "x \<in> \<tau>"
  proof (induction x rule: Tstar.induct)
    case (2 x y)
    then have "computation q0 x q0"
      using computation.intros(2)[OF delta.intros(1) computation.intros(2)[OF delta.intros(4)],
          OF computation.intros(1)]
        computation.intros(2)[OF delta.intros(1) computation.intros(2)[OF delta.intros(5)],
          OF computation.intros(1)]
        computation.intros(2)[OF delta.intros(3) computation.intros(2)[OF delta.intros(7)],
          OF computation.intros(1)]
      by (cases x) (auto simp: T_def)
    then show ?case
      using 2(3)
      by (cases x, cases y) (auto simp: \<tau>_def comp_trans)
  qed (auto simp: \<tau>_def)
qed

lemma active_q1_dest: "active q1 bs \<Longrightarrow> \<exists>bs' bs''. bs @ bs' = b # a # bs''"
  by (auto simp: active_def dest!: comp_q1_dest)

lemma active_q2_dest: "active q2 bs \<Longrightarrow> \<exists>bs' bs''. bs @ bs' = a # b # bs''"
  by (auto simp: active_def dest!: comp_q2_dest)

lemma active_q3_dest: "active q3 bs \<Longrightarrow> \<exists>bs' bs''. bs @ bs' = a # a # bs''"
  by (auto simp: active_def dest!: comp_q3_dest)

lemma comp_q0_dest:
  assumes "computation q0 (x # y # zs, v) q"
  shows "\<exists>v' v''. v = v' @ v'' \<and> ([x, y], v') \<in> T \<and> computation q0 (zs, v'') q"
  apply (rule computation.cases[OF assms])
   apply (auto simp: T_def elim!: delta.cases dest!: comp_q1_dest comp_q2_dest comp_q3_dest)
     apply (metis append.simps(1) append.simps(2))+
  done

lemma bt:
  assumes "computation q0 (u, v @ v') q" "active q []" "computation q0 (u, v) q'" "active q' v'"
  shows "length v' \<le> Suc 0"
  using assms
proof (induction u arbitrary: v v' rule: induct_list012)
  case (3 x y zs)
  obtain w' w'' where v_split: "v = w' @ w''" "([x, y], w') \<in> T" "computation q0 (zs, w'') q'"
    using comp_q0_dest[OF 3(5)]
    by auto
  obtain z' z'' where vv'_split: "v @ v' = z' @ z''" "([x, y], z') \<in> T"
    "computation q0 (zs, z'') q"
    using comp_q0_dest[OF 3(3)]
    by auto
  show ?case
  proof (cases "w' = z'")
    case True
    have z''_def: "z'' = w'' @ v'"
      using vv'_split(1)
      by (auto simp: v_split(1) True)
    show ?thesis
      by (rule 3(1)[OF vv'_split(3)[unfolded z''_def] 3(4) v_split(3) 3(6)])
  next
    case False
    then have "(w' = [a, b, a, b, a] \<and> z' = [a, b, a, b, a, b]) \<or>
      (w' = [a, b, a, b, a, b] \<and> z' = [a, b, a, b, a])"
      using v_split(2) vv'_split(2)
      by (auto simp: T_def)
    then show ?thesis
    proof (rule disjE)
      assume "w' = [a, b, a, b, a] \<and> z' = [a, b, a, b, a, b]"
      then have z''_def: "w'' @ v' = b # z''"
        using vv'_split(1)[unfolded v_split(1)]
        by auto
      show "length v' \<le> Suc 0"
        apply (rule computation.cases[OF v_split(3)])
        using z''_def no_step[OF vv'_split(3)]
        by (auto elim: delta.cases)
    next
      assume "w' = [a, b, a, b, a, b] \<and> z' = [a, b, a, b, a]"
      then have z''_def: "z'' = b # w'' @ v'"
        using vv'_split(1)[unfolded v_split(1)]
        by auto
      show "length v' \<le> Suc 0"
        apply (rule computation.cases[OF vv'_split(3)])
        using z''_def
        by (auto elim: delta.cases)
    qed
  qed
qed (auto elim!: computation.cases delta.cases)

interpretation bNFT q0 delta "\<lambda>q. q = q0" UNIV 1
  by unfold_locales (auto simp add: bounded_def bt)

lemma tdfa_init: "tdfa_init = STATE ([], {(q0, 0)})"
  using comp_q0_qf
  by (auto simp add: tdfa_init_def active_def)

lemma delta_length: "delta x y z \<Longrightarrow> length (snd z) \<in> {2, 3, 4}"
  by (auto elim: delta.cases)

lemma delta_length': "n \<in> {2, 3, 4} \<Longrightarrow> \<exists>x y z. delta x y z \<and> length (snd z) = n"
  using delta.intros
  by fastforce

lemma output_speed: "output_speed = 4"
proof -
  have "length ` snd ` {x. \<exists>a b. delta a b x} = {2, 3, 4}"
    using delta_length delta_length'
    by auto (metis imageI mem_Collect_eq snd_conv)+
  then show ?thesis
    by (auto simp add: output_speed_def all_trans_def)
qed

lemma K': "K' = 5"
  unfolding K'_def output_speed by auto

(* Figure 3b *)

lemma step_1: "tdfa_step tdfa_init (Symb a, Symb a) = Some (STATE ([a], {(q0, 0)}), False, True)"
  "STATE ([a], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs a [] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step tdfa_init (Symb a, Symb a) = Some (STATE ([a], {(q0, 0)}), False, True)"
    using init_in_tdfa_Q[unfolded tdfa_init] ext_qs[symmetric]
    unfolding tdfa_step.simps tdfa_init K'
    by (simp add: drop_qs)
  then show "STATE ([a], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF init_in_tdfa_Q[unfolded tdfa_init]]
    by (auto simp add: tdfa_init)
qed

lemma step_2: "tdfa_step (STATE ([a], {(q0, 0)})) (Symb a, Symb b) =
  Some (STATE ([a, b], {(q0, 0)}), False, True)" "STATE ([a, b], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs b [a] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (STATE ([a], {(q0, 0)})) (Symb a, Symb b) =
    Some (STATE ([a, b], {(q0, 0)}), False, True)"
    using step_1(2) ext_qs[symmetric]
    unfolding tdfa_step.simps K'
    by (simp add: drop_qs)
  then show "STATE ([a, b], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_1(2)]
    by auto
qed

lemma step_3: "tdfa_step (STATE ([a, b], {(q0, 0)})) (Symb a, Symb a) =
  Some (STATE ([a, b, a], {(q0, 0)}), False, True)" "STATE ([a, b, a], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs a [a, b] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (STATE ([a, b], {(q0, 0)})) (Symb a, Symb a) =
    Some (STATE ([a, b, a], {(q0, 0)}), False, True)"
    using step_2(2) ext_qs[symmetric]
    unfolding tdfa_step.simps K'
    by (simp add: drop_qs)
  then show "STATE ([a, b, a], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_2(2)]
    by auto
qed

lemma step_4: "tdfa_step (STATE ([a, b, a], {(q0, 0)})) (Symb a, Symb b) =
  Some (STATE ([a, b, a, b], {(q0, 0)}), False, True)" "STATE ([a, b, a, b], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs b [a, b, a] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (STATE ([a, b, a], {(q0, 0)})) (Symb a, Symb b) =
    Some (STATE ([a, b, a, b], {(q0, 0)}), False, True)"
    using step_3(2) ext_qs[symmetric]
    unfolding tdfa_step.simps K'
    by (simp add: drop_qs)
  then show "STATE ([a, b, a, b], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_3(2)]
    by auto
qed

lemma step_5: "tdfa_step (STATE ([a, b, a, b], {(q0, 0)})) (Symb a, Symb a) =
  Some (STATE ([a, b, a, b, a], {(q0, 0)}), False, True)"
  "STATE ([a, b, a, b, a], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs a [a, b, a, b] {(q0, 0)} = {(q0, 0)}"
    using comp_trans[OF one_step[OF delta.intros(1)] one_step[OF delta.intros(4)]]
    by (fastforce simp add: ext_qs_def active_def)
  have drop_qs: "drop_qs 0 {(q0, 0)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (STATE ([a, b, a, b], {(q0, 0)})) (Symb a, Symb a) =
    Some (STATE ([a, b, a, b, a], {(q0, 0)}), False, True)"
    using step_4(2) ext_qs[symmetric]
    unfolding tdfa_step.simps K'
    by (simp add: drop_qs)
  then show "STATE ([a, b, a, b, a], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_4(2)]
    by auto
qed

lemma take_length: "n \<le> Suc (Suc (Suc (Suc (Suc 0)))) \<Longrightarrow> take n [a, b, a, b, a] = ys \<Longrightarrow>
  n = length ys"
  by auto

lemma step_6: "tdfa_step (STATE ([a, b, a, b, a], {(q0, 0)})) (Symb a, Symb b) =
  Some (STATE ([b, a], {(q1, 0), (q2, 1), (q3, 1)}), True, False)"
  "STATE ([b, a], {(q1, 0), (q2, 1), (q3, 1)}) \<in> tdfa_Q"
proof -
  have act_q1: "active q1 [b, a]"
    using one_step[OF delta.intros(4)]
    by (auto simp add: active_def)
  have act_q2: "active q2 [a]"
    using one_step[OF delta.intros(6)]
    by (auto simp add: active_def)
  have act_q3: "active q3 [a]"
    using one_step[OF delta.intros(7)]
    by (auto simp add: active_def)
  have upd_qs: "upd_qs a [a, b, a, b, a] {(q0, 0)} = {(q1, 3), (q2, 4), (q3, 4)}"
    by (auto simp add: upd_qs_def elim!: delta.cases
        dest: active_q1_dest active_q2_dest active_q3_dest take_length
        intro: delta.intros act_q1 act_q2 act_q3)
  have drop_qs: "drop_qs 3 {(q1, 3), (q2, 4), (q3, 4)} =
    {(q1, 0), (q2, 1), (q3, 1)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (STATE ([a, b, a, b, a], {(q0, 0)})) (Symb a, Symb b) =
    Some (STATE ([b, a], {(q1, 0), (q2, 1), (q3, 1)}), True, False)"
    using step_5(2)
    unfolding tdfa_step.simps K'
    by (simp add: upd_qs drop_qs Let_def)
  then show "STATE ([b, a], {(q1, 0), (q2, 1), (q3, 1)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_5(2)]
    by auto
qed

lemma step_7: "tdfa_step (STATE ([b, a], {(q1, 0), (q2, 1), (q3, 1)})) (Symb a, Symb b) =
  Some (STATE ([b, a, b], {(q1, 0), (q2, 1)}), False, True)"
  "STATE ([b, a, b], {(q1, 0), (q2, 1)}) \<in> tdfa_Q"
proof -
  have ext_qs: "ext_qs b [b, a] {(q1, 0), (q2, 1), (q3, 1)} = {(q1, 0), (q2, 1)}"
    using one_step[OF delta.intros(5)] one_step[OF delta.intros(6)]
    by (fastforce simp add: ext_qs_def active_def dest!: comp_q3_dest)
  have drop_qs: "drop_qs 0 {(q1, 0), (q2, 1)} = {(q1, 0), (q2, 1)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (STATE ([b, a], {(q1, 0), (q2, 1), (q3, 1)})) (Symb a, Symb b) =
    Some (STATE ([b, a, b], {(q1, 0), (q2, 1)}), False, True)"
    using step_6(2) drop_qs
    unfolding tdfa_step.simps ext_qs K'
    by (simp add: ext_qs Let_def)
  then show "STATE ([b, a, b], {(q1, 0), (q2, 1)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_6(2)]
    by auto
qed

lemma step_8: "tdfa_step (STATE ([b, a, b], {(q1, 0), (q2, 1)})) (Symb a, Blank) =
  Some (STATE ([], {(q0, 0)}), True, False)"
  "STATE ([], {(q0, 0)}) \<in> tdfa_Q"
proof -
  have act_qf: "active q0 []"
    by (auto simp add: active_def)
  have active_q0_b_dest: "\<And>zs. active q0 (b # zs) \<Longrightarrow> False"
    by (auto simp: active_def elim: computation.cases elim!: delta.cases)
  have upd_qs: "upd_qs a [b, a, b] {(q1, 0), (q2, 1)} = {(q0, 3)}"
    using active_q0_b_dest
    apply (auto simp add: upd_qs_def elim!: delta.cases intro: delta.intros act_qf)
      apply (metis One_nat_def diff_self_eq_0 drop0 drop_Suc_Cons le_SucE le_zero_eq
        list.distinct(1) list.sel(3) numeral_3_eq_3 take_Cons')
     apply (metis diff_is_0_eq' drop_eq_Nil drop_take dual_order.antisym length_Cons list.size(3)
        numeral_3_eq_3 order_refl take_eq_Nil)
    apply (metis One_nat_def Suc_diff_le diff_is_0_eq' le_SucE list.distinct(1) list.sel(3)
        numeral_3_eq_3 take_Cons')
    done
  have drop_qs: "drop_qs 3 {(q0, 3)} = {(q0, 0)}"
    by (auto simp add: drop_qs_def)
  show "tdfa_step (STATE ([b, a, b], {(q1, 0), (q2, 1)})) (Symb a, Blank) =
    Some (STATE ([], {(q0, 0)}), True, False)"
    using step_7(2) upd_qs
    unfolding tdfa_step.simps K'
    by (simp add: drop_qs)
  then show "STATE ([], {(q0, 0)}) \<in> tdfa_Q"
    using tdfa_closed[OF step_7(2)]
    by auto
qed

interpretation tdfa: TDFA tdfa_init tdfa_step tdfa_accept tdfa_Q
  using tdfa_axioms .

lemma comp_correct: "([a, a], [a, b, a, b, a, b]) \<in> tdfa.\<tau>"
proof -
  have "tdfa.computation tdfa_init (([a, a], []), [a, b, a, b, a, b], []) (STATE ([], {(q0, 0)}))"
    apply (rule tdfa.computation.intros(4)[rotated, OF tdfa.computation.intros(4),
        rotated, OF tdfa.computation.intros(4), rotated, OF tdfa.computation.intros(4),
        rotated, OF tdfa.computation.intros(4), rotated, OF tdfa.computation.intros(3),
        rotated, OF tdfa.computation.intros(4), rotated, OF tdfa.computation.intros(3),
        rotated, OF tdfa.computation.intros(1)])
    using step_1(1) step_2(1) step_3(1) step_4(1) step_5(1) step_6(1) step_7(1) step_8(1)
    by (auto simp: safe_hd_def)
  then show ?thesis
    unfolding tdfa.\<tau>_def tdfa_accept_def
    by auto
qed

end
