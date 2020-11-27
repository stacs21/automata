theory Necessary
  imports Computation
begin

locale necessary' = knft: kNFT ninit n\<delta> naccept nQ + koTDFA init \<delta> accept Q
  for ninit :: "'s"
  and n\<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> 'b list \<Rightarrow> bool"
  and naccept :: "'s \<Rightarrow> bool"
  and nQ :: "'s set"
  and init :: "'t"
  and \<delta> :: "'t \<Rightarrow> ('a :: finite) Al \<times> 'b Al \<Rightarrow> ('t \<times> bool \<times> bool) option"
  and accept :: "'t \<Rightarrow> bool"
  and Q :: "'t set" +
assumes equiv: "knft.\<tau> = \<tau>"
begin

abbreviation f\<delta> :: "'t \<Rightarrow> 'b Al \<times> 'a Al \<Rightarrow> ('t \<times> bool \<times> bool) option" where
  "f\<delta> \<equiv> (\<lambda>q (b, a). case \<delta> q (a, b) of None \<Rightarrow> None | Some (q', b1, b2) \<Rightarrow> Some (q', b2, b1))"

interpretation flip: oTDFA init f\<delta> accept Q
  using finite_Q init_in_Q closed move_left move_right no_step move_one
  apply unfold_locales
        apply (auto split: option.splits)
     apply fastforce+
  done

lemma flip_comp_intro: "q \<leadsto>(as, bs) q' \<Longrightarrow> flip.computation q (bs, as) q'"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct) auto

lemma flip_comp_dest: "flip.computation q (bs, as) q' \<Longrightarrow> q \<leadsto>(as, bs) q'"
  by (induction q "(bs, as)" q' arbitrary: as bs rule: flip.computation.induct)
     (auto split: option.splits)

lemma flip_comp_eq: "flip.computation q (bs, as) q' \<longleftrightarrow> q \<leadsto>(as, bs) q'"
  using flip_comp_intro flip_comp_dest
  by blast

lemmas flip_comp_to_states = flip.comp_to_states[unfolded flip_comp_eq]
lemmas flip_states_to_comp = flip.states_to_comp[unfolded flip_comp_eq]
lemmas flip_split_outs = flip.split_outs[unfolded flip_comp_eq]

lemma split_long:
  assumes "length w \<ge> n"
  shows "\<exists>v' v''. w = v' @ v'' \<and> length v'' = n"
  using assms
  by (metis append_take_drop_id diff_diff_cancel length_drop)

lemma concat_filter: "length qbs = length xs \<Longrightarrow> length ns = length xs \<Longrightarrow>
  concat (map (\<lambda>(n, (q, bs), tqs). bs) (filter (\<lambda>(n, (q, bs), tqs). bs \<noteq> [])
  (zip ns (zip qbs xs)))) = concat (map snd qbs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma concat_length: "(\<And>n q bs tqs. (n, (q, bs), tqs) \<in> set qss' \<Longrightarrow> length bs \<le> d) \<Longrightarrow>
  length (concat (map (\<lambda>(n, (q, bs), tqs). bs) qss')) \<le> length qss' * d"
  by (induction qss') fastforce+

lemma sorted_dest: "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow> i < j \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i < xs ! j"
  by (simp add: less_le nth_eq_iff_index_eq sorted_iff_nth_mono_less)

lemma map2_zip: "length qbs = length xs \<Longrightarrow> length qbs = length ns \<Longrightarrow>
  qbs = map2 (\<lambda>n ((q, bs), tqs). (q, bs)) ns (zip qbs xs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma map2_zip': "length qbs = length xs \<Longrightarrow> length qbs = length ns \<Longrightarrow>
  xs = map2 (\<lambda>n ((q, bs), (bs', q')). (bs', q')) ns (zip qbs xs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma split_one: "n < length xs \<Longrightarrow> \<exists>ys ys'. xs = ys @ (xs ! n) # ys' \<and>
  length ys = n \<and> length ys' = length xs - (n + 1)"
  apply (induction n arbitrary: xs)
  subgoal for xs
    by (cases xs) auto
  subgoal for n xs
    apply (cases xs)
     apply auto
    apply (metis append_Cons length_Cons)
    done
  done

lemma split_two: "n < n' \<Longrightarrow> n' < length xs \<Longrightarrow>
  \<exists>ys ys' ys''. xs = ys @ (xs ! n) # ys' @ (xs ! n') # ys'' \<and> length ys = n \<and>
  length ys' = n' - (n + 1) \<and> length ys'' = length xs - (n' + 1)"
proof (induction n arbitrary: n' xs)
  case 0
  then show ?case
  proof (cases xs)
    case (Cons x xs')
    then show ?thesis
      using 0 split_one[of "n' - 1" xs']
      by auto
  qed auto
next
  case (Suc n)
  then show ?case
  proof (cases xs)
    case (Cons x xs')
    have n'_shift: "n < n' - 1" "n' - 1 < length xs'"
      using Suc(2,3)
      by (auto simp add: Cons)
    then obtain ys ys' ys'' where split: "xs' = ys @ xs' ! n # ys' @ xs' ! (n' - 1) # ys''"
      "length ys = n" "length ys' = n' - (Suc n + 1)" "length ys'' = length xs - (n' + 1)"
      using Suc(1)[OF n'_shift]
      by (auto simp add: Cons)
    show ?thesis
      apply (rule exI[of _ "x # ys"])
      using split Suc(2)
      by (auto simp add: Cons)
  qed auto
qed

lemma wits:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>w. P w x"
  shows "\<exists>ws. length ws = length xs \<and> (\<forall>(w, x) \<in> set (zip ws xs). P w x)"
  using assms
proof (induction xs)
  case (Cons x xs)
  obtain w where w_def: "P w x"
    using Cons(2)
    by auto
  obtain ws where ws_def: "length ws = length xs"
    "\<And>a. a \<in> set (zip ws xs) \<Longrightarrow> case a of (a, b) \<Rightarrow> P a b"
    using Cons
    by fastforce
  show ?case
    using w_def ws_def
    by (auto intro!: exI[of _ "w # ws"])
qed auto

definition "sel1 \<equiv> \<lambda>a. case a of (x, y, z) \<Rightarrow> x"
definition "sel1' \<equiv> \<lambda>x y z. x"
definition "sel2 \<equiv> \<lambda>a. case a of (x, y, z) \<Rightarrow> y"
definition "sel2' \<equiv> \<lambda>x y z. y"
definition "sel3 \<equiv> \<lambda>a. case a of (x, y, z) \<Rightarrow> z"
definition "sel3' \<equiv> \<lambda>x y z. z"
definition "sel4 \<equiv> \<lambda>a. case a of (x, y, z, w) \<Rightarrow> z"
definition "sel4' \<equiv> \<lambda>a. case a of (x, y, z, w) \<Rightarrow> w"

lemma wits3:
  assumes "\<And>x y z. (x, y, z) \<in> set xs \<Longrightarrow> \<exists>w. P w x y z"
  shows "\<exists>ws. length ws = length xs \<and> (\<forall>(w, x, y, z) \<in> set (zip ws xs). P w x y z)"
  using wits[OF assms, of _ sel1 sel2 sel3]
  by (fastforce simp: sel1_def sel2_def sel3_def)

fun trans :: "nat \<Rightarrow> 'x list list \<Rightarrow> 'x list list" where
  "trans 0 xss = []"
| "trans (Suc n) xss = map hd xss # trans n (map tl xss)"

lemma len_trans: "length (trans n xss) = n"
  by (induction n xss rule: trans.induct) auto

lemma set_trans: "(\<And>xs. xs \<in> set xss \<Longrightarrow> set xs \<subseteq> Q \<and> length xs = n) \<Longrightarrow>
  set (trans n xss) \<subseteq> {ys. set ys \<subseteq> Q \<and> length ys = length xss}"
proof (induction n xss rule: trans.induct)
  case (2 n xss)
  have "set (trans n (map tl xss)) \<subseteq> {ys. set ys \<subseteq> Q \<and> length ys = length (map tl xss)}"
    apply (rule 2(1))
    apply (auto dest!: 2(2))
    apply (metis list.sel(2) list.set_sel(2) subsetD)
    done
  then show ?case
    using 2(2)
    by auto (metis length_greater_0_conv list.set_sel(1) subsetD zero_less_Suc)
qed auto

lemma trans_nth: "(\<And>xs. xs \<in> set xss \<Longrightarrow> length xs = n) \<Longrightarrow>
  i < n \<Longrightarrow> j < length xss \<Longrightarrow> trans n xss ! i ! j = xss ! j ! i"
  apply (induction n xss arbitrary: i j rule: trans.induct)
   apply auto
  by (smt One_nat_def Suc_pred hd_conv_nth imageE length_0_conv length_tl less_Suc_eq_0_disj
      nat.inject nat.simps(3) nth_Cons_0 nth_Cons_Suc nth_map nth_mem nth_tl)

lemma one_loop_aux:
  assumes "knft.computation s (u, v) s'" "s \<in> nQ"
    "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r (([], w), (u, u')) r'"
    "set (map (fst \<circ> snd) ws) \<subseteq> Q"
    "length v \<ge> (card nQ * card Q ^ length ws) * knft.output_speed + 1"
  shows "\<exists>u'' v''. length v'' < length v \<and> knft.computation s (u'', v'') s' \<and>
    (\<forall>(w, r, r') \<in> set ws. flip.computation r (([], w), (u'', u')) r') \<and>
    safe_hd u = safe_hd u'' \<and> safe_hd v = safe_hd v''"
proof -
  obtain qbs where qbs_def: "knft.computation_ext s (u, qbs) s'" "v = concat (map snd qbs)"
    using knft.computation_ext_complete[OF assms(1)]
    by auto
  note qbs_output_speed = knft.output_speed_ext_computation[OF qbs_def(1) assms(2)]
  have len_qbs: "length qbs = length u"
    using knft.computation_ext_length[OF qbs_def(1)]
    by auto
  obtain tqss' where tqss'_def: "length tqss' = length ws"
    "\<And>tqs w r r'. (tqs, w, r, r') \<in> set (zip tqss' ws) \<Longrightarrow>
      flip.computation_ext r (tqs, ([], w), (u, u')) r'"
    using wits3[OF flip.comp_to_ext[OF assms(3)]]
    by fastforce
  have set_tqss': "\<And>tqs w r r'. (tqs, w, r, r') \<in> set (zip tqss' ws) \<Longrightarrow> set tqs \<subseteq> Q"
    apply (rule flip.ext_closed[OF tqss'_def(2)])
    using assms(4)
    by (auto simp: comp_def dest!: set_zip_rightD)
  have len_tqss': "\<And>tqs w r r'. (tqs, w, r, r') \<in> set (zip tqss' ws) \<Longrightarrow> length tqs = length u"
    using flip.comp_ext_length[OF tqss'_def(2)]
    by auto
  define tqss where "tqss = trans (length u) tqss'"
  define qss where "qss = zip [0..<length qbs] (zip qbs tqss)"
  have len_tqss: "length tqss = length u"
    by (auto simp: tqss_def len_trans)
  have len_qss: "length qss = length qbs"
    using len_qbs len_tqss
    by (auto simp: qss_def)
  have fst_qss_at: "\<And>i. i < length qss \<Longrightarrow> fst (qss ! i) = i"
    using len_qbs
    by (auto simp: qss_def)
  have fst_set_qss: "\<And>x. x \<in> set qss \<Longrightarrow> fst x < length qss"
    using len_qbs len_tqss
    by (auto simp: qss_def dest: set_zip_leftD)
  define qss' where "qss' = filter (\<lambda>(n, (q, bs), tqs). bs \<noteq> []) qss"
  have fst_set_qss': "\<And>x. x \<in> set qss' \<Longrightarrow> x \<in> set qss"
    by (auto simp: qss'_def)
  define qs where "qs = map (\<lambda>(n, (q, bs), tqs). (q, tqs)) qss'"
  have qss'_at: "\<And>i. i < length qss' \<Longrightarrow>
    fst (qss' ! i) < length qss \<and> qss' ! i = qss ! (fst (qss' ! i))"
    using fst_qss_at fst_set_qss' fst_set_qss
    by auto (metis fst_set_qss' in_set_conv_nth)
  have qss'_nonempty: "\<And>n q bs tqs. (n, (q, bs), tqs) \<in> set qss' \<Longrightarrow> bs \<noteq> []"
    by (auto simp: qss'_def)
  have sorted_fst_qss: "sorted (map fst qss)" "distinct (map fst qss)"
    using len_qbs len_tqss
    by (auto simp: qss_def)
  have sorted_fst_qss': "sorted (map fst qss')" "distinct (map fst qss')"
    unfolding qss'_def
    by (rule sorted_filter[OF sorted_fst_qss(1)])
       (rule distinct_map_filter[OF sorted_fst_qss(2)])
  have len_qs: "length qs = length qss'"
    by (auto simp add: qs_def)
  have set_qbs: "\<And>q bs. (q, bs) \<in> set qbs \<Longrightarrow> q \<in> nQ"
    using knft.computation_ext_closed[OF qbs_def(1) assms(2)]
    by auto
  have tqs_tqss': "\<And>tqs. tqs \<in> set tqss' \<Longrightarrow> set tqs \<subseteq> Q \<and> length tqs = length u"
  proof -
    fix tqs
    assume "tqs \<in> set tqss'"
    then obtain i where i_def: "i < length tqss'" "tqss' ! i = tqs"
      by (auto simp: in_set_conv_nth)
    then have "(tqs, fst (ws ! i), fst (snd (ws ! i)), snd (snd (ws ! i))) \<in> set (zip tqss' ws)"
      using tqss'_def(1)
      by (auto simp: in_set_conv_nth)
    then show "set tqs \<subseteq> Q \<and> length tqs = length u"
      using len_tqss' set_tqss'
      by blast
  qed
  have concat_qss': "concat (map (\<lambda>(n, (q, bs), tqs). bs) qss') = concat (map snd qbs)"
    using concat_filter[of qbs tqss "[0..<length qbs]"] len_qbs len_tqss
    by (auto simp: qss'_def qss_def)
  have len_v_le: "length v \<le> length qss' * knft.output_speed"
    unfolding arg_cong[OF concat_qss', symmetric] qbs_def(2)
    apply (rule concat_length[of qss' knft.output_speed])
    using qbs_output_speed
    by (auto simp: qss'_def qss_def dest: set_zip_leftD set_zip_rightD)
  have len_qs_ge: "length qs \<ge> card nQ * card Q ^ length ws + 1"
  proof (rule ccontr)
    assume "\<not>length qs \<ge> card nQ * card Q ^ length ws + 1"
    then have "length qs * knft.output_speed \<le>
      (card nQ * (card Q ^ (length ws))) * knft.output_speed"
      using knft.output_speed_pos
      by simp
    then show "False"
      using le_trans[OF assms(5) len_v_le] le_trans
      unfolding len_qs[symmetric]
      by linarith
  qed
  have qs_sub: "set qs \<subseteq> nQ \<times> {tqs. set tqs \<subseteq> Q \<and> length tqs = length ws}"
    using set_qbs set_trans[OF tqs_tqss'] len_qbs len_tqss tqss'_def(1)
    by (fastforce simp: qs_def qss'_def qss_def tqss_def dest: set_zip_leftD set_zip_rightD)
  have not_distinct: "\<not> distinct qs"
  proof (rule ccontr)
    assume "\<not>\<not> distinct qs"
    then have contr: "distinct qs"
      by auto
    have card_qs: "card (set qs) \<ge> card nQ * card Q ^ length ws + 1"
      using distinct_card[OF contr] len_qs_ge
      by (auto simp add: qs_def)
    have finite_lists: "finite {tqs. set tqs \<subseteq> Q \<and> length tqs = length ws}"
      and card_lists: "card {tqs. set tqs \<subseteq> Q \<and> length tqs = length ws} = (card Q) ^ (length ws)"
      using finite_lists_length_eq[OF finite_Q, of "length ws"]
        card_lists_length_eq[OF finite_Q, of "length ws"]
      by auto
    have finite_prod: "finite (nQ \<times> {tqs. set tqs \<subseteq> Q \<and> length tqs = length ws})"
      using knft.finite_Q finite_lists
      by blast
    have card_prod: "card (nQ \<times> {tqs. set tqs \<subseteq> Q \<and> length tqs = length ws}) =
      card nQ * (card Q) ^ (length ws)"
      unfolding card_cartesian_product card_lists ..
    show "False"
      using card_qs card_mono[OF finite_prod qs_sub]
      by (auto simp add: card_prod)
  qed
  obtain qc qs' qs'' qs''' where qs_split: "qs = qs' @ [qc] @ qs'' @ [qc] @ qs'''"
    using not_distinct_decomp[OF not_distinct]
    by auto
  define n where "n = fst (qss' ! length qs')"
  define n' where "n' = fst (qss' ! (length qs' + 1 + length qs''))"
  have valid_idx: "length qs' < length qss'" "length qs' + 1 + length qs'' < length qss'"
    using qs_split len_qs len_qss
    by auto
  have qs_split_at: "qs ! (length qs') = qc" "qs ! (length qs' + 1 + length qs'') = qc"
    using qs_split
     apply auto
    by (metis add_Suc_right nth_Cons_Suc nth_append_length nth_append_length_plus)
  have n_n': "n < n'" "n' < length qbs" "qss ! n = qss' ! length qs'"
    "qss ! n' = qss' ! (length qs' + 1 + length qs'')"
    using qss'_at[OF valid_idx(1), folded n_def] qss'_at[OF valid_idx(2), folded n'_def]
          len_qss valid_idx sorted_dest[OF sorted_fst_qss']
    by (auto simp add: n_def n'_def)
  have n_len_u: "n < length u" "n' < length u"
    using n_n'(1,2) len_qbs
    by auto
  have qbs_map: "qbs = map (\<lambda>(n, (q, bs), tqs). (q, bs)) qss"
    using map2_zip[of qbs tqss "[0..<length qbs]"] len_qbs len_tqss
    by (auto simp add: qss_def)
  obtain qbs' qbs'' qbs''' where decomp: "qbs = qbs' @ qbs ! n # qbs'' @ qbs ! n' # qbs'''"
    "length qbs' = n" "length qbs'' = n' - (n + 1)" "length qbs''' = length qbs - (n' + 1)"
    using split_two[OF n_n'(1,2)]
    by auto
  obtain bs' where bs'_def: "qbs ! n = (fst qc, bs')" "bs' \<noteq> []"
    using qbs_map n_n' qs_def len_qs qs_split_at(1) valid_idx(1) qss'_nonempty
    by (auto split: prod.splits) (metis in_set_conv_nth)
  obtain bs'' where bs''_def: "qbs ! n' = (fst qc, bs'')" "bs'' \<noteq> []"
    using qbs_map n_n' qs_def len_qs qs_split_at(2) valid_idx(2) qss'_nonempty
    by (auto split: prod.splits) (metis in_set_conv_nth)
  have tqss_n: "tqss ! n = snd qc"
    using qs_split_at(1) qs_def qss'_at[OF valid_idx(1), folded n_def] valid_idx(1)
    by (auto simp: qss_def split: prod.splits)
  have tqss_n': "tqss ! n' = snd qc"
    using qs_split_at(2) qs_def qss'_at[OF valid_idx(2), folded n'_def] valid_idx(2)
    by (auto simp: qss_def split: prod.splits)
  obtain cs' cs'' cs''' c' c'' bs'a bs''' where new_comp:
    "knft.computation s (cs' @ c' # cs''', bs'a @ bs' @ bs''') s'"
    "bs'a = concat (map snd qbs')" "bs''' = concat (map snd qbs''')"
    "u = cs' @ c' # cs'' @ c'' # cs'''" "length cs' = length qbs'" "length cs'' = length qbs''"
    "length cs''' = length qbs'''"
    using knft.computation_ext_rem[OF qbs_def(1)[unfolded decomp(1)[unfolded bs'_def bs''_def]]]
    by auto
  have new_length: "length (bs'a @ bs' @ bs''') < length v"
    apply (auto simp add: new_comp(2,3) qbs_def(2))
    apply (subst decomp(1))
    apply (auto simp add: bs'_def bs''_def)
    done
  have rem_tqss': "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow>
    flip.computation r (([], w), cs' @ c' # cs''', u') r'"
  proof -
    fix w r r'
    assume in_set: "(w, r, r') \<in> set ws"
    then obtain i where i_def: "i < length ws" "(w, r, r') = ws ! i"
      using tqss'_def(1)
      by (auto simp: in_set_conv_nth)
    define tqs where "tqs = tqss' ! i"
    have in_set_zip: "(tqs, w, r, r') \<in> set (zip tqss' ws)"
      using in_set i_def tqss'_def(1)
      by (auto simp: in_set_conv_nth tqs_def)
    note len_tqs = len_tqss'[OF in_set_zip]
    have trans_n: "trans (length u) tqss' ! n ! i = tqss' ! i ! n"
      apply (rule trans_nth)
      using tqs_tqss' n_len_u(1) i_def(1) tqss'_def(1)
      by auto
    have trans_n': "trans (length u) tqss' ! n' ! i = tqss' ! i ! n'"
      apply (rule trans_nth)
      using tqs_tqss' n_len_u(2) i_def(1) tqss'_def(1)
      by auto
    have tqs_n_n': "tqs ! n = tqs ! n'"
      using tqss_n tqss_n'
      unfolding tqs_def trans_n[symmetric] trans_n'[symmetric] tqss_def[symmetric]
      by auto
    obtain ys ys' ys'' where tqs_split:
      "tqs = ys @ tqs ! n # ys' @ tqs ! n # ys''"
      "length ys = n" "length ys' = n' - (n + 1)" "length ys'' = length tqs - (n' + 1)"
      using split_two[of n n' tqs] n_n'(1,2) len_qbs len_tqs
      by (auto simp: tqs_n_n')
    have comp_orig: "flip.computation_ext r
      (ys @ tqs ! n # ys' @ tqs ! n # ys'', ([], w), cs' @ c' # cs'' @ c'' # cs''', u') r'"
      using tqss'_def(2)[OF in_set_zip, unfolded new_comp(4)]
      unfolding tqs_split(1)[symmetric] .
    have comp_new: "flip.computation_ext r (ys @ tqs ! n # ys'', ([], w), cs' @ c' # cs''', u') r'"
      using flip.ext_rem_loop[OF comp_orig] tqs_split(2,3)
      by (auto simp: decomp(2,3) new_comp(5,6))
    show "flip.computation r (([], w), cs' @ c' # cs''', u') r'"
      using flip.ext_to_comp[OF comp_new] .
  qed
  have "safe_hd u = safe_hd (cs' @ c' # cs''')"
    unfolding new_comp(4)
    by (simp add: safe_hd_app_Cons)
  moreover have "safe_hd v = safe_hd (bs'a @ bs' @ bs''')"
    unfolding qbs_def(2)
    apply (subst decomp(1))
    using safe_hd_app'' bs'_def(2)
    by (force simp: bs'_def(1) new_comp(2))
  ultimately show ?thesis
    using new_length new_comp(1) rem_tqss'
    by blast
qed

definition tcard :: "nat \<Rightarrow> nat" where
  "tcard n = (card nQ * card Q ^ n + 1) * knft.output_speed"

lemma one_loop:
  assumes "knft.computation s (u, v @ v') s'" "s \<in> nQ"
    "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r (([], w), (u, u')) r'"
    "set (map (fst \<circ> snd) ws) \<subseteq> Q" "length v \<ge> tcard (length ws) + 1"
  shows "\<exists>u'' v''. length v'' < length v \<and> knft.computation s (u'', v'' @ v') s' \<and>
    (\<forall>(w, r, r') \<in> set ws. flip.computation r (([], w), (u'', u')) r') \<and>
    safe_hd u = safe_hd u'' \<and> safe_hd (v @ v') = safe_hd (v'' @ v')"
proof -
  obtain s'' as as' cs cs' where split:
    "knft.computation s (as, cs) s''" "knft.computation s'' (as', cs') s'"
    "u = as @ as'" "v @ v' = cs @ cs'" "length cs \<le> length v"
    "length v - length cs \<le> knft.output_speed"
    using knft.computation_split_out[OF assms(1,2)]
    by auto
  obtain es where v_def: "v = cs @ es"
    using split_app[OF split(4)[symmetric] split(5)]
    by auto
  have cs'_def: "cs' = es @ v'"
    using split(4)
    by (auto simp: v_def)
  obtain rs'' where rs''_def: "length rs'' = length ws"
    "\<And>r'' w r r'. (r'', w, r, r') \<in> set (zip rs'' ws) \<Longrightarrow>
      flip.computation r (([], w), as, as' @ u') r'' \<and> flip.computation r'' (([], w), as', u') r'"
    using wits3[OF flip.comp_splitL[OF assms(3)[unfolded split(3)]], of ws sel1' sel2' sel3']
    by (auto simp: sel1'_def sel2'_def sel3'_def split: prod.splits)
  define ws' where "ws' = map (\<lambda>(r'', w, r, r'). (w, r, r'')) (zip rs'' ws)"
  have ws'_Q: "set (map (fst \<circ> snd) ws') \<subseteq> Q"
    using assms(4) rs''_def(1)
    by (auto simp: ws'_def dest!: set_zip_rightD)
  have comp_ws': "\<And>w r r'. (w, r, r') \<in> set ws' \<Longrightarrow> flip.computation r (([], w), as, as' @ u') r'"
    using rs''_def
    by (auto simp: ws'_def)
  have len_ws': "length ws' = length ws"
    using rs''_def(1)
    by (auto simp: ws'_def)
  have len_cs: "(card nQ * card Q ^ length ws') * knft.output_speed + 1 \<le> length cs"
    using assms(5) split(5,6)
    unfolding len_ws'
    by (auto simp: tcard_def)
  obtain u'' v'' where rem: "length v'' < length cs"
    "knft.computation s (u'', v'') s''"
    "\<And>w r r'. (w, r, r') \<in> set ws' \<Longrightarrow> flip.computation r (([], w), u'', as' @ u') r'"
    "safe_hd as = safe_hd u''" "safe_hd cs = safe_hd v''"
    using one_loop_aux[OF split(1) assms(2) comp_ws' ws'_Q len_cs]
    by fastforce
  have F1: "length (v'' @ es) < length v"
    using rem(1)
    by (auto simp: v_def)
  have F3: "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r (([], w), u'' @ as', u') r'"
  proof -
    fix w r r'
    assume "(w, r, r') \<in> set ws"
    then obtain i where i_def: "i < length ws" "ws ! i = (w, r, r')"
      by (auto simp: in_set_conv_nth)
    define r'' where "r'' = rs'' ! i"
    have "(w, r, r'') \<in> set ws'"
      using rs''_def(1) i_def
      by (auto simp: ws'_def r''_def)
         (smt case_prod_conv image_iff len_ws' length_map nth_mem nth_zip ws'_def)
    then have comp1: "flip.computation r (([], w), u'', as' @ u') r''"
      using rem(3)
      by auto
    have "(r'', w, r, r') \<in> set (zip rs'' ws)"
      using rs''_def(1) i_def
      by (auto simp: r''_def in_set_conv_nth)
    then have comp2: "flip.computation r'' (([], w), as', u') r'"
      using rs''_def(2)
      by auto
    show "flip.computation r (([], w), u'' @ as', u') r'"
      using flip.comp_transR[OF comp1 comp2] .
  qed
  have F4: "safe_hd (as @ as') = safe_hd (u'' @ as')"
    using rem(4) safe_hd_app
    by auto
  have F5: "safe_hd (cs @ es @ v') = safe_hd ((v'' @ es) @ v')"
    using rem(5) safe_hd_app
    by auto
  show ?thesis
    apply (rule exI[of _ "u'' @ as'"])
    apply (rule exI[of _ "v'' @ es"])
    using F1 knft.comp_trans[OF rem(2) split(2)] F3 F4 F5
    unfolding split(3,4) cs'_def
    by auto
qed

lemma one_conflict_aux:
  assumes "knft.computation s (u, v @ v') s'" "s \<in> nQ"
    "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r ((w, []), (u, [])) r'"
    "set (map (fst \<circ> snd) ws) \<subseteq> Q"
    "length v \<ge> tcard (length ws) * (length (concat (map fst ws)) + 1) + 1"
  shows "\<exists>u'' v''. length v'' < length v \<and> knft.computation s (u'', v'' @ v') s' \<and>
    (\<forall>(w, r, r') \<in> set ws. flip.computation r ((w, []), (u'', [])) r') \<and>
    safe_hd u = safe_hd u'' \<and> safe_hd (v @ v') = safe_hd (v'' @ v')"
  using assms
proof (induction "length (concat (map fst ws))" arbitrary: ws s u v)
  case 0
  have comp: "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r (([], w), u, []) r'"
    using 0(1,4)
    by auto
  have len_v: "tcard (length ws) + 1 \<le> length v"
    using 0(1,6)
    by auto
  obtain u'' v'' where rem: "length v'' < length v"
    "knft.computation s (u'', v'' @ v') s'"
    "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r (([], w), u'', []) r'"
    "safe_hd u = safe_hd u''" "safe_hd (v @ v') = safe_hd (v'' @ v')"
    using one_loop[OF 0(2,3) comp 0(5) len_v]
    by fastforce
  have new_comp: "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r ((w, []), u'', []) r'"
    using 0(1) rem(3)
    by auto
  show ?case
    using rem(1,2) new_comp rem(4,5)
    by fastforce
next
  case (Suc l)
  obtain cs cs' ts where wss_def: "u = cs @ cs'" "length ts = length ws"
    "\<And>w r t r'. (t, w, r, r') \<in> set (zip ts ws) \<Longrightarrow>
      flip.computation r (([], w), (cs, cs')) t \<and> flip.computation t ((w, []), (cs', [])) r'"
    "\<exists>(t, w, r, r') \<in> set (zip ts ws). \<exists>t'.
        f\<delta> t (safe_hd w, safe_hd cs') = Some (t', True, False)"
    using flip.split_outss[of ws, OF Suc(5), simplified] Suc(2)
    by (fastforce split: list.splits prod.splits)
  obtain s'' bs bs' where knft_split: "knft.computation s (cs, bs) s''"
    "knft.computation s'' (cs', bs') s'" "v @ v' = bs @ bs'"
    using knft.computation_split[OF Suc(3)[unfolded wss_def(1)]]
    by auto
  have v_def: "v = take (length v) (bs @ bs')"
    using knft_split(3) append_eq_conv_conj
    by blast
  have v'_def: "v' = drop (length v) (bs @ bs')"
    using knft_split(3) append_eq_conv_conj
    by blast
  define vm where "vm = tcard (length ws) + 1"
  have vm_len_v: "vm \<le> length v"
    using Suc(7)
    by (auto simp: vm_def)
  show ?case
  proof (cases "length bs \<ge> vm")
    case True
    define es where "es = take vm bs"
    define es' where "es' = drop vm bs"
    define es'' where "es'' = drop vm (take (length v) (bs @ bs'))"
    have bs_def: "bs = es @ es'"
      using True
      by (simp add: es'_def es_def)
    have v_def': "v = es @ es''"
      using vm_len_v
      apply (subst v_def)
      apply (cases "length bs \<ge> length v")
       apply (auto simp: es_def es''_def True)
      apply (metis drop_take le_add_diff_inverse take_add)
      done
    define ws' where "ws' = map (\<lambda>(t, w, r, r'). (w, r, t)) (zip ts ws)"
    have len_ws': "length ws' = length ws"
      using wss_def(2)
      by (auto simp: ws'_def)
    have comp_ws': "\<And>w r r'. (w, r, r') \<in> set ws' \<Longrightarrow> flip.computation r (([], w), cs, cs') r'"
      using wss_def(2,3)
      by (auto simp: ws'_def)
    have ws'_Q: "set (map (fst \<circ> snd) ws') \<subseteq> Q"
      using Suc(6)
      by (auto simp: ws'_def dest!: set_zip_rightD)
    have len_es: "tcard (length ws') + 1 \<le> length es"
      using True
      by (auto simp: len_ws' es_def vm_def)
    obtain u'' v'' where rem:
      "length v'' < length es" "knft.computation s (u'', v'' @ es') s''"
      "\<And>w r r'. (w, r, r') \<in> set ws' \<Longrightarrow> flip.computation r (([], w), u'', cs') r'"
      "safe_hd cs = safe_hd u''" "safe_hd (es @ es') = safe_hd (v'' @ es')"
      using one_loop[OF knft_split(1)[unfolded bs_def] Suc(4) comp_ws' ws'_Q len_es]
      by fastforce
    have "v @ v' = (es @ es'') @ v'"
      using v_def'
      by auto
    then have v''_app: "(v'' @ es') @ bs' = (v'' @ es'') @ v'"
      unfolding bs_def knft_split(3)
      by simp
    have F1: "length (v'' @ es'') < length v"
      using rem(1)
      by (auto simp: v_def')
    have F3: "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r ((w, []), u'' @ cs', []) r'"
    proof -
      fix w r r'
      assume "(w, r, r') \<in> set ws"
      then obtain i where i_def: "i < length ws" "ws ! i = (w, r, r')"
        by (auto simp: in_set_conv_nth)
      have in_set_zip_ts_ws: "(ts ! i, w, r, r') \<in> set (zip ts ws)"
        using wss_def(2) i_def(1)
        unfolding i_def(2)[symmetric]
        by (auto simp: in_set_conv_nth)
      then have comp_old: "flip.computation r (([], w), cs, cs') (ts ! i)"
        "flip.computation (ts ! i) ((w, []), cs', []) r'"
        using wss_def(3)
        by auto
      have comp_new: "flip.computation r (([], w), u'', cs') (ts ! i)"
        apply (rule rem(3))
        using in_set_zip_ts_ws image_iff
        by (force simp: ws'_def)
      show "flip.computation r ((w, []), u'' @ cs', []) r'"
        using flip.comp_trans[OF comp_new comp_old(2)]
        by auto
    qed
    have F4: "safe_hd (cs @ cs') = safe_hd (u'' @ cs')"
      using rem(4) safe_hd_app
      by auto
    have F5: "safe_hd ((es @ es') @ bs') = safe_hd ((v'' @ es') @ bs')"
      using rem(5) safe_hd_app
      by fastforce
    show ?thesis
      apply (rule exI[of _ "u'' @ cs'"])
      apply (rule exI[of _ "v'' @ es''"])
      using F1 knft.comp_trans[OF rem(2) knft_split(2)] F3 F4 F5
      unfolding v''_app[symmetric] wss_def(1) knft_split(3) bs_def
      by auto
  next
    case False
    obtain es where es_def: "v = bs @ es"
      using split_app[OF knft_split(3)[symmetric]] False Suc(7)
      by (auto simp: vm_def)
    have bs'_def: "bs' = es @ v'"
      using knft_split(3)
      by (auto simp: es_def)
    obtain i t' where i_def: "i < length ts"
      "f\<delta> (ts ! i) (safe_hd (fst (ws ! i)), safe_hd cs') = Some (t', True, False)"
      using wss_def(2,4)
      by (auto simp: in_set_conv_nth)
    obtain x xs where wsi_def: "fst (ws ! i) = x # xs"
      using flip.move_left[OF i_def(2)]
      by (auto simp: safe_hd_def split: list.splits)
    define ts' where "ts' = take i ts @ t' # drop (Suc i) ts"
    define ws' where "ws' = take i (map fst ws) @ tl (fst (ws ! i)) # drop (Suc i) (map fst ws)"
    define rs' where "rs' = map (\<lambda>(_, _, r'). r') ws"
    define wss' where "wss' = zip ws' (zip ts' rs')"
    have len': "length ts' = length ts" "length ws' = length ts" "length rs' = length ts"
      "length wss' = length ws"
      using i_def(1) wss_def(2)
      by (auto simp: ts'_def ws'_def rs'_def wss'_def)
    have map_fst_wss': "map fst wss' = ws'"
      using len'
      by (auto simp: wss'_def)
    have "length (concat (map fst ws)) = length (concat (take i (map fst ws))) +
      (Suc (length xs) + length (concat (drop (Suc i) (map fst ws))))"
      using i_def(1) wss_def(2)
        arg_cong[of _ _ "\<lambda>x. length (concat (map fst x))", OF id_take_nth_drop[of i ws]]
      by (auto simp: wsi_def take_map drop_map)
    then have l_def: "l = length (concat (map fst wss'))"
      using Suc(2)
      by (auto simp: map_fst_wss' ws'_def wsi_def)
    have comp_wss': "\<And>w r r'. (w, r, r') \<in> set wss' \<Longrightarrow> flip.computation r ((w, []), cs', []) r'"
    proof -
      fix w r r'
      assume "(w, r, r') \<in> set wss'"
      then obtain j where j_def: "j < length ws" "w = ws' ! j" "r = ts' ! j" "r' = rs' ! j"
        using len'
        by (auto simp: wss'_def in_set_conv_nth)
      show "flip.computation r ((w, []), cs', []) r'"
      proof (cases "j = i")
        case True
        have "case ws ! i of (w, _, r') \<Rightarrow> flip.computation (ts ! i) ((w, []), cs', []) r'"
          using i_def(1) wss_def(2,3)
          by (fastforce simp: in_set_conv_nth)
        then show ?thesis
          using i_def wss_def(2) wsi_def
          by (auto simp: j_def(2,3,4) True ts'_def ws'_def rs'_def nth_append safe_hd_def
              split: option.splits elim: flip.computation.cases)
      next
        case False
        have "(r, w, fst (snd (ws ! j)), r') \<in> set (zip ts ws)"
          using False i_def(1) wss_def(2) j_def
          by (auto simp: ws'_def ts'_def rs'_def nth_append min_def in_set_conv_nth
              split: prod.splits)
        then show ?thesis
          using wss_def(3)
          by auto
      qed
    qed
    have len_es: "tcard (length wss') * (length (concat (map fst wss')) + 1) + 1 \<le> length es"
      using Suc(7)[unfolded es_def] False
      by (auto simp: Suc(2)[symmetric] l_def[symmetric] len'(4) vm_def)
    note s''_nQ = knft.comp_closed[OF knft_split(1) Suc(4)]
    have wss'_Q: "set (map (fst \<circ> snd) wss') \<subseteq> Q"
    proof (rule subsetI)
      fix q
      assume "q \<in> set (map (fst \<circ> snd) wss')"
      then obtain j where j_def: "j < length ws" "q = ts' ! j"
        using len'
        by (auto simp: wss'_def in_set_conv_nth)
      show "q \<in> Q"
      proof (cases "j = i")
        case True
        have "(ts ! i, fst (ws ! i), fst (snd (ws ! i)), snd (snd (ws ! i))) \<in> set (zip ts ws)"
          using i_def(1) wss_def(2)
          by (auto simp: in_set_conv_nth)
        then have "flip.computation (fst (snd (ws ! i))) (([], fst (ws ! i)), cs, cs') (ts ! i)"
          using wss_def(3)
          by fastforce
        then have "ts ! i \<in> Q"
          apply (rule flip.comp_closed)
          using Suc(6) i_def(1) wss_def(2)
          by auto
        then show ?thesis
          using flip.closed[OF _ i_def(2)] i_def(1)
          by (auto simp: j_def(2) True ts'_def nth_append min_def)
      next
        case False
        have "(q, fst (ws ! j), fst (snd (ws ! j)), snd (snd (ws ! j))) \<in> set (zip ts ws)"
          using j_def(1) wss_def(2) False
          by (auto simp: in_set_conv_nth j_def(2) ts'_def nth_append min_def split: prod.splits)
        then have "flip.computation (fst (snd (ws ! j))) (([], fst (ws ! j)), cs, cs') q"
          using wss_def(3)
          by fastforce
        then show ?thesis
          apply (rule flip.comp_closed)
          using Suc(6) j_def(1)
          by auto
      qed
    qed
    obtain u'' v'' where ind: "length v'' < length es"
      "knft.computation s'' (u'', v'' @ v') s'"
      "\<And>w r r'. (w, r, r') \<in> set wss' \<Longrightarrow> flip.computation r ((w, []), u'', []) r'"
      "safe_hd cs' = safe_hd u''" "safe_hd (es @ v') = safe_hd (v'' @ v')"
      using Suc(1)[OF l_def knft_split(2)[unfolded bs'_def] s''_nQ comp_wss' wss'_Q len_es]
      by fastforce
    have flip_comp_trans: "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow>
      flip.computation r ((w, []), cs @ u'', []) r'"
    proof -
      fix w r r'
      assume "(w, r, r') \<in> set ws"
      then obtain j where j_def: "j < length ws" "ws ! j = (w, r, r')"
        by (auto simp: in_set_conv_nth)
      have comp_fst: "flip.computation r (([], w), cs, cs') (ts ! j)"
        apply (rule conjunct1[OF wss_def(3)])
        using j_def wss_def(2)
        by (auto simp: in_set_conv_nth)
      show "flip.computation r ((w, []), cs @ u'', []) r'"
      proof (cases "j = i")
        case True
        have w_def: "w = x # xs"
          using j_def(2) wsi_def
          by (auto simp: True)
        have "(xs, t', r') \<in> set wss'"
          using i_def(1) wss_def(2) j_def(2) len' wsi_def
          by (auto simp: in_set_conv_nth True wss'_def ws'_def ts'_def rs'_def nth_append min_def)
        then have comp_snd': "flip.computation t' ((xs, []), u'', []) r'"
          using ind(3)
          by auto
        have comp_snd: "flip.computation (ts ! i) ((w, []), u'', []) r'"
          unfolding w_def
          apply (rule flip.step_TF[OF _ comp_snd'])
          using i_def(2)
          by (auto simp: wsi_def ind(4) safe_hd_Cons)
        show ?thesis
          using flip.comp_trans[OF comp_fst[unfolded True] comp_snd] ind(4)
          by auto
      next
        case False
        have "(w, ts ! j, r') \<in> set wss'"
          using i_def(1) wss_def(2) j_def len' False
          by (auto simp: in_set_conv_nth wss'_def ws'_def ts'_def rs'_def nth_append min_def)
        then have comp_snd: "flip.computation (ts ! j) ((w, []), u'', []) r'"
          using ind(3)
          by auto
        show ?thesis
          using flip.comp_trans[OF comp_fst comp_snd] ind(4)
          by auto
      qed
    qed
    show ?thesis
      apply (rule exI[of _ "cs @ u''"])
      apply (rule exI[of _ "bs @ v''"])
      using ind(1) knft.comp_trans[OF knft_split(1) ind(2)] flip_comp_trans ind(4,5)
      by (auto simp: es_def wss_def(1) intro: safe_hd_app')
  qed
qed

lemma one_conflict:
  assumes "knft.computation s (u, v) s'" "s \<in> nQ"
    "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> flip.computation r ((w, []), (u, [])) r'"
    "set (map (fst \<circ> snd) ws) \<subseteq> Q"
    "length v \<ge> tcard (length ws) * (length (concat (map fst ws)) + 1) + 1"
  shows "\<exists>u'' v''. length v'' < length v \<and>
    length v - (tcard (length ws) * (length (concat (map fst ws)) + 1) + 1) \<le> length v'' \<and>
    knft.computation s (u'', v'') s' \<and>
    (\<forall>(w, r, r') \<in> set ws. flip.computation r ((w, []), (u'', [])) r') \<and>
    safe_hd u = safe_hd u'' \<and> safe_hd v = safe_hd v''"
proof -
  define l where "l = tcard (length ws) * (length (concat (map fst ws)) + 1) + 1"
  have knft_comp: "knft.computation s (u, take l v @ drop l v) s'"
    using assms(1)
    by auto
  have len_take: "tcard (length ws) * (length (concat (map fst ws)) + 1) + 1 \<le> length (take l v)"
    using assms(5)
    by (auto simp: l_def)
  obtain u'' v'' where aux: "length v'' < length (take l v)"
    "knft.computation s (u'', v'' @ drop l v) s'"
    "\<forall>(w, r, r')\<in>set ws. flip.computation r ((w, []), u'', []) r'"
    "safe_hd u = safe_hd u''" "safe_hd (take l v @ drop l v) = safe_hd (v'' @ drop l v)"
    using one_conflict_aux[OF knft_comp assms(2,3,4) len_take]
    by auto
  show ?thesis
    apply (rule exI[of _ u''])
    apply (rule exI[of _ "v'' @ drop l v"])
    using aux
    by (auto simp add: l_def)
qed

fun minv :: "nat \<Rightarrow> nat" where
  "minv 0 = (knft.sg + 1) * (card Q + 1) + (knft.sg + 1) * knft.output_speed"
| "minv (Suc n) = tcard (Suc n) * ((sum_list (map minv [0..<Suc n]) + knft.output_speed) *
    Suc n + 1) + knft.output_speed + 1"

declare minv.simps[simp del]

definition sminv :: "nat \<Rightarrow> nat" where
  "sminv n = sum_list (map minv [0..<Suc n])"

lemma sminv_Suc: "sminv (Suc n) = sminv n + minv (Suc n)"
  by (auto simp: sminv_def)

lemma sminv_ge_zero: "minv 0 \<le> sminv n"
  by (induction n) (auto simp: sminv_def)

lemma tcard_pos: "tcard x \<ge> 1"
  using knft.output_speed_pos
  by (auto simp: tcard_def)

lemma sminv_Suc_ge_os: "knft.output_speed \<le> sminv (Suc n)"
  by (auto simp: sminv_Suc minv.simps)

lemma minv_Suc_ge_sminv_os: "sminv n + 2 * knft.output_speed \<le> minv (Suc n)"
proof -
  have "sum_list (map minv [0..<n]) + minv n + knft.output_speed \<le>
    tcard (Suc n) * (sum_list (map minv [0..<n]) + minv n + knft.output_speed)"
    using tcard_pos[of "Suc n"]
    by auto
  moreover have "\<dots> \<le> tcard (Suc n) * (sum_list (map minv [0..<n]) + minv n + knft.output_speed +
    (sum_list (map minv [0..<n]) + minv n + knft.output_speed) * n)"
    by auto
  finally show ?thesis
    by (auto simp: minv.simps(2) sminv_def)
qed

lemma length_concat_le:
  "(\<And>ws. ws \<in> set wss \<Longrightarrow> length ws \<le> n) \<Longrightarrow> length (concat wss) \<le> n * length wss"
  by (induction wss) fastforce+

lemma trans_list:
  assumes "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>x'. P x x' \<and> P' x')"
  shows "\<exists>xs'. length xs = length xs' \<and> (\<forall>(x, x') \<in> set (zip xs xs'). P x x') \<and>
    (\<forall>x' \<in> set xs'. P' x')"
  using assms
proof (induction xs)
  case (Cons x xs)
  obtain x' xs' where "P x x'" "P' x'"
    "length xs = length xs'" "\<forall>(x, x') \<in> set (zip xs xs'). P x x'" "\<forall>x' \<in> set xs'. P' x'"
    using Cons
    by fastforce
  then show ?case
    by (auto intro!: exI[of _ "x' # xs'"] split: prod.splits)
qed auto

lemma map_cong': "length xs = length xs' \<Longrightarrow>
  (\<And>x x'. (x, x') \<in> set (zip xs xs') \<Longrightarrow> f x = f' x') \<Longrightarrow> map f xs = map f' xs'"
  by (induction xs xs' rule: list_induct2) auto

lemma distinct_inj: "inj f \<Longrightarrow> distinct xs \<Longrightarrow> distinct (map f xs)"
  by (induction xs) (auto simp: inj_def)

lemma conflict_rec:
  assumes "knft.computation ninit (u0, v0) s" "knft.computation s (u, v @ v') s'" "naccept s'"
    "init \<leadsto>((u0, u), (v0 @ v, v')) r" "r \<leadsto>((u, []), (v', [])) r'" "accept r'"
    "length v' \<le> minv 0" "sminv n \<le> length (v @ v')"
    "length (v @ v') \<le> sminv n + knft.output_speed"
  shows "\<exists>u'' v'' ws. safe_hd u = safe_hd u'' \<and> length ws = n \<and>
    knft.computation s (u'', v'') s' \<and>
    length v'' \<le> length (v @ v') \<and> distinct (map (\<lambda>(cv, cw, r, r'). length (cv @ cw)) ws) \<and>
    (\<forall>(cv, cw, r, r') \<in> set ws. init \<leadsto>((u0, u''), (v0 @ cv, cw)) r \<and>
      r \<leadsto>((u'', []), (cw, [])) r' \<and> accept r' \<and>
      length v'' < length (cv @ cw) \<and> length (cv @ cw) \<le> length (v @ v'))"
  using assms(1,2,4,5,7,8,9)
proof (induction n arbitrary: u0 v0 s u v v' r)
  case 0
  show ?case
    apply (rule exI[of _ u])
    apply (rule exI[of _ "v @ v'"])
    apply (rule exI[of _ "[]"])
    using 0
    by (auto simp: sminv_def)
next
  case (Suc n)
  have len_v'_le_sminv: "length v' \<le> sminv n"
    using Suc(6) sminv_ge_zero[of n]
    by auto
  have "length v' \<le> minv (Suc n)"
    using Suc(6) sminv_ge_zero[of n] minv_Suc_ge_sminv_os[of n]
    by auto
  then have len_v_ge_sminv: "length v \<ge> sminv n"
    using Suc(7) minv_Suc_ge_sminv_os[of n]
    by (auto simp: sminv_Suc)
  then have "length v \<ge> sminv n - length v'"
    by simp
  then obtain es es' where es_def: "v = es @ es'"
    "length es' = sminv n - length v'"
    using split_long
    by blast
  have len_es_eq: "length es = length v - sminv n + length v'"
    using len_v_ge_sminv len_v'_le_sminv
    by (auto simp: es_def)
  moreover have "\<dots> \<ge> minv ((Suc n))"
    using Suc(7)
    by (auto simp: sminv_Suc)
  finally have len_es_ge: "minv ((Suc n)) \<le> length es" .
  have len_es_le: "length es \<le> minv ((Suc n)) + knft.output_speed"
    using Suc(8)[unfolded es_def(1)]
    by (auto simp: es_def(2) sminv_Suc)
  have knft_es: "knft.computation s (u, es @ es' @ v') s'"
    using Suc(3)
    by (auto simp: es_def(1))
  note s_nQ = knft.comp_closed[OF Suc(2) knft.init_in_Q]
  obtain s'' as as' cs cs' where knft_split:
    "knft.computation s (as, cs) s''" "knft.computation s'' (as', cs') s'"
    "u = as @ as'" "es @ es' @ v' = cs @ cs'" "length cs \<le> length es"
    "length es - length cs \<le> knft.output_speed"
    using knft.computation_split_out[OF knft_es s_nQ]
    by auto
  note s''_nQ = knft.comp_closed[OF knft_split(1) s_nQ]
  obtain fs' where es_split: "es = cs @ fs'" "cs' = fs' @ es' @ v'"
    using knft_split(4,5)
    by (metis append_eq_append_conv_if append_eq_conv_conj)
  have len_fs': "length fs' \<le> knft.output_speed"
    using knft_split(6)
    by (auto simp: es_split(1))
  obtain r'' ds ds' where tdfa_split: "v' = ds @ ds'" "r\<leadsto>((as, as' @ []), ds, ds' @ [])r''"
    "r''\<leadsto>((as', []), ds', [])r'"
    using comp_split[OF Suc(5)[unfolded knft_split(3)]]
    by auto
  note knft_fst = knft.comp_trans[OF Suc(2) knft_split(1)]
  have knft_snd: "knft.computation s'' (as', (fs' @ es' @ ds) @ ds') s'"
    using knft_split(2)
    by (auto simp: es_split(2) tdfa_split(1))
  have tdfa_fst: "init \<leadsto>((u0 @ as, as'), (v0 @ cs) @ fs' @ es' @ ds, ds')r''"
    using comp_trans[OF Suc(4) tdfa_split(2)]
    by (auto simp: knft_split(3) tdfa_split(1) es_def(1) es_split(1,2))
  have sminv_le: "sminv n \<le> length ((fs' @ es' @ ds) @ ds')"
    using Suc(7) es_def(2)
    by (auto simp: es_def(1) tdfa_split(1) sminv_Suc)
  have sminv_ge: "length ((fs' @ es' @ ds) @ ds') \<le> sminv n + knft.output_speed"
    using len_v'_le_sminv len_fs'
    by (auto simp: es_def(2) tdfa_split(1))
  have len_ds': "length ds' \<le> minv 0"
    using Suc(6)
    by (auto simp: tdfa_split(1))
  obtain u'' v'' ws where rec: "safe_hd as' = safe_hd u''" "length ws = n"
    "knft.computation s'' (u'', v'') s'"
    "length v'' \<le> length ((fs' @ es' @ ds) @ ds')"
    "distinct (map (\<lambda>(cv, cw, r, r'). length (cv @ cw)) ws)"
    "\<And>cv cw r r'. (cv, cw, r, r') \<in> set ws \<Longrightarrow> init\<leadsto>((u0 @ as, u''), (v0 @ cs) @ cv, cw)r \<and>
      r\<leadsto>((u'', []), cw, [])r' \<and> accept r' \<and> length v'' < length (cv @ cw) \<and>
      length (cv @ cw) \<le> length ((fs' @ es' @ ds) @ ds')"
    using Suc(1)[OF knft_fst knft_snd tdfa_fst tdfa_split(3) len_ds' sminv_le sminv_ge]
    by fastforce
  have safe_hd_u''_as: "safe_hd (as @ u'') = safe_hd u"
    using safe_hd_app'[OF rec(1)]
    by (auto simp: knft_split(3))
  obtain ws' where ws'_def: "length ws = length ws'" "\<forall>(x, x')\<in>set (zip ws ws').
    case x of (cv, cw, r, r') \<Rightarrow> case x' of (cv', cw', s, s') \<Rightarrow> cs @ cv @ cw = cv' @ cw'"
    "\<forall>x' \<in> set ws'. case x' of (cv', cw', s, s') \<Rightarrow> init\<leadsto>((u0, as @ u''), v0 @ cv', cw')s \<and>
      s\<leadsto>((as @ u'', []), cw', [])s' \<and> accept s' \<and> length (cs @ v'') < length (cv' @ cw') \<and>
      length (cv' @ cw') \<le> length (v @ v') \<and> length cw' \<le> sminv n + knft.output_speed"
  proof (atomize_elim, rule trans_list)
    fix x
    assume x_in_ws: "x \<in> set ws"
    obtain cv cw cr cr' where x_def: "x = (cv, cw, cr, cr')"
      by (cases x) auto
    have comp_cr_cr': "cr\<leadsto>((u'', []), cw, [])cr'"
      using rec(6) x_in_ws
      by (auto simp: x_def)
    note rec_props = rec(6)[OF x_in_ws[unfolded x_def]]
    obtain nv nw ns where ns_def: "cv = nv @ nw"
      "init\<leadsto>((u0, as @ u''), (v0 @ cs) @ nv, nw @ cw)ns" "ns\<leadsto>((as, u''), nw, cw)cr"
      using det_comp_safe[OF conjunct1[OF rec_props] _ safe_hd_u''_as]
        Suc(4)
      by (fastforce simp: es_def es_split(1))
    have len_cv_cw: "length nv + length nw + length cw \<le> length ((fs' @ es' @ ds) @ ds')"
      using rec_props
      by (auto simp: ns_def(1))
    have len_v_v'_ge: "length cs + length nv + (length nw + length cw) \<le> length v + length v'"
      using len_cv_cw
      by (auto simp: es_def(1) tdfa_split(1) es_split(1))
    have comp_init_ns: "init\<leadsto>((u0, as @ u''), v0 @ cs @ nv, nw @ cw)ns"
      using ns_def(2) safe_hd_app'[OF rec(1)] comp_swap_same_hd
      by auto
    have comp_ns_cr': "ns\<leadsto>((as @ u'', []), nw @ cw, [])cr'"
      using comp_trans[OF ns_def(3) comp_cr_cr'] rec(1)
      by auto
    show "\<exists>x'. (case x of (cv, cw, r, r') \<Rightarrow> case x' of (cv', cw', s, s') \<Rightarrow>
        cs @ cv @ cw = cv' @ cw') \<and>
      (case x' of (cv', cw', s, s') \<Rightarrow> init\<leadsto>((u0, as @ u''), v0 @ cv', cw')s \<and>
        s\<leadsto>((as @ u'', []), cw', [])s' \<and> accept s' \<and> length (cs @ v'') < length (cv' @ cw') \<and>
        length (cv' @ cw') \<le> length (v @ v') \<and> length cw' \<le> sminv n + knft.output_speed)"
      apply (rule exI[of _ "(cs @ nv, nw @ cw, ns, cr')"])
      using ns_def rec_props knft_split(5) comp_init_ns comp_ns_cr' len_v_v'_ge sminv_ge
      by (auto simp: x_def)
  qed
  have set_ws'_dest: "\<And>cv' cw' s s'. (cv', cw', s, s') \<in> set ws' \<Longrightarrow>
    init\<leadsto>((u0, as @ u''), v0 @ cv', cw')s \<and> s\<leadsto>((as @ u'', []), cw', [])s' \<and> accept s' \<and>
    length (cs @ v'') < length (cv' @ cw') \<and> length (cv' @ cw') \<le> length (v @ v') \<and>
    length cw' \<le> sminv n + knft.output_speed"
    using ws'_def
    by auto
  have "(u0 @ as @ u'', v0 @ cs @ v'') \<in> \<tau>"
    using knft.comp_trans[OF Suc(2) knft.comp_trans[OF knft_split(1) rec(3)]] assms(3)
    by (auto simp: knft.\<tau>_def equiv[symmetric])
  then obtain nr' where new_comp: "init \<leadsto>((u0 @ as @ u'', []), ((v0 @ cs) @ v'', [])) nr'"
    "accept nr'"
    by (auto simp: \<tau>_def)
  have safe_hd_u_as: "safe_hd u = safe_hd (as @ u'')"
    using safe_hd_app' rec(1)
    by (fastforce simp: knft_split(3))
  obtain nw nw' nr where nr_def: "v'' = nw @ nw'" "init\<leadsto>((u0, as @ u''), (v0 @ cs) @ nw, nw')nr"
    "nr\<leadsto>((as @ u'', []), nw', [])nr'"
    apply atomize_elim
    using det_comp_safe[OF new_comp(1)] Suc(4) safe_hd_u_as
    by (auto simp: es_def(1) es_split(1))
  have len_nw': "length nw' \<le> sminv n + knft.output_speed"
    using rec(4) sminv_ge
    by (auto simp: nr_def(1))
  define nws where "nws = ws' @ [(cs @ nw, nw', nr, nr')]"
  have len_nws: "length nws = Suc n"
    by (auto simp: nws_def ws'_def(1)[symmetric] rec(2))
  have flip_comp: "\<And>cw r r'. (cw, r, r') \<in> set (map snd nws) \<Longrightarrow>
    flip.computation r ((cw, []), as @ u'', []) r'"
    using nr_def(3)
    by (auto simp: flip_comp_eq nws_def dest: set_ws'_dest)
  have tdfa_closed: "set (map (fst \<circ> snd) (map snd nws)) \<subseteq> Q"
    using comp_closed[OF _ init_in_Q] nr_def(2)
    by (auto simp: nws_def dest: set_ws'_dest)
  have len_ws_rw: "length ws = length (map fst (map snd ws))"
    by auto
  note comp_s_s' = knft.comp_trans[OF knft_split(1) rec(3)]
  have length_nws_ws: "length nws = length (map fst (map snd nws))"
    by auto
  have len_concat_sminv: "length (concat (map fst (map snd nws))) \<le>
    (sminv n + knft.output_speed) * length nws"
    apply (subst length_nws_ws)
    apply (rule length_concat_le)
    using len_nw'
    by (auto simp: nws_def dest: set_ws'_dest)
  have len_cs_v'': "tcard (length (map snd nws)) *
    (length (concat (map fst (map snd nws))) + 1) + 1 \<le> length (cs @ v'')"
  proof -
    have "tcard (length (map snd nws)) * (length (concat (map fst (map snd nws))) + 1) + 1 \<le>
      tcard (Suc n) * ((sminv n + knft.output_speed) * length nws + 1) + 1"
      using len_concat_sminv
      by (auto simp: len_nws)
    moreover have "\<dots> \<le> minv (Suc n) - knft.output_speed"
      unfolding sminv_Suc minv.simps sminv_def[symmetric] len_nws
      using knft.output_speed_pos
      by simp
    finally show ?thesis
      using knft_split(6) len_es_ge
      by simp
  qed
  obtain u''' v''' where conflict: "length v''' < length (cs @ v'')"
    "length (cs @ v'') - (tcard (length (map snd nws)) *
      (length (concat (map fst (map snd nws))) + 1) + 1)  \<le> length v'''"
    "knft.computation s (u''', v''') s'"
    "(\<forall>(w, r, r')\<in>set (map snd nws). r \<leadsto>((u''', []), (w, [])) r')"
    "safe_hd (as @ u'') = safe_hd u'''" "safe_hd (cs @ v'') = safe_hd v'''"
    using one_conflict[OF comp_s_s' s_nQ flip_comp tdfa_closed len_cs_v'']
    by (auto simp: flip_comp_eq)
  have safe_hd_u_u''': "safe_hd u = safe_hd u'''"
    using safe_hd_u_as conflict(5)
    by auto
  have nr_swap: "init\<leadsto>((u0, u'''), (v0 @ cs) @ nw, nw')nr"
    using nr_def(2) comp_swap_same_hd[OF _ conflict(5) refl]
    by simp
  have len_cs_v''_le: "length (cs @ v'') \<le> length (v @ v')"
    using knft_split(4) rec(4)
    by (auto simp: es_def(1) es_split(2) tdfa_split(1))
  then have len_v'''_le: "length v''' \<le> length (v @ v')"
    using conflict(1)
    by auto
  have M1: "map (\<lambda>(cv, cw, r, r'). length (cs @ cv @ cw)) ws =
    map (\<lambda>n. length cs + n) (map (\<lambda>(cv, cw, r, r'). length (cv @ cw)) ws)"
    by auto
  have M2: "map (\<lambda>(cv, cw, r, r'). length (cs @ cv @ cw)) ws =
    map (\<lambda>(cv, cw, r, r'). length (cv @ cw)) ws'"
    apply (rule map_cong'[OF ws'_def(1)])
    using ws'_def(2)
    by fastforce
  have "distinct (map (\<lambda>a. case a of (cv, cw, r, r') \<Rightarrow> length (cv @ cw)) ws')"
    unfolding M2[symmetric] M1
    by (rule distinct_inj[OF _ rec(5)]) (simp add: inj_def)
  then have distinct_nws: "distinct (map (\<lambda>a. case a of (cv, cw, r, r') \<Rightarrow> length (cv @ cw)) nws)"
    by (auto simp: nws_def nr_def(1) dest!: set_ws'_dest)
  have nws_props: "\<forall>a\<in>set nws. case a of (cv, cw, r, r') \<Rightarrow>
    init\<leadsto>((u0, u'''), v0 @ cv, cw)r \<and> r\<leadsto>((u''', []), cw, [])r' \<and>
    accept r' \<and> length v''' < length (cv @ cw) \<and> length (cv @ cw) \<le> length (v @ v')"
    using nr_swap new_comp(2) conflict(1,4) len_cs_v''_le comp_swap_same_hd[OF _ conflict(5) refl]
      set_ws'_dest
    by (fastforce simp: nws_def nr_def(1))
  show ?case
    apply (rule exI[of _ "u'''"])
    apply (rule exI[of _ "v'''"])
    apply (rule exI[of _ nws])
    using safe_hd_u_u''' len_nws conflict(3) len_v'''_le distinct_nws nws_props
    by simp
qed

lemma conflict:
  assumes "knft.computation ninit (u0, v0) s" "knft.computation s (u, v @ v') s'" "naccept s'"
    "init \<leadsto>((u0, u), (v0 @ v, v')) r" "r \<leadsto>((u, []), (v', [])) r'" "accept r'"
    "length v' \<le> minv 0" "sminv n \<le> length (v @ v')"
  shows "\<exists>u'' v'' ws. length ws = Suc n \<and> distinct ws \<and>
    (\<forall>cw \<in> set ws. (u0 @ u'', v0 @ v'' @ cw) \<in> \<tau>)"
proof -
  obtain es es' where es_def: "v @ v' = es @ es'"
    "length es' = sminv n"
    using split_long assms(8)
    by blast
  note s_nQ = knft.comp_closed[OF assms(1) knft.init_in_Q]
  obtain s'' as as' cs cs' where knft_split:
    "knft.computation s (as, cs) s''" "knft.computation s'' (as', cs') s'"
    "u = as @ as'" "es @ es' = cs @ cs'" "length cs \<le> length es"
    "length es - length cs \<le> knft.output_speed"
    using knft.computation_split_out[OF assms(2)[unfolded es_def(1)] s_nQ]
    by auto
  obtain r'' fs fs' where tdfa_split: "v' = fs @ fs'" "r\<leadsto>((as, as'), fs, fs')r''"
    "r''\<leadsto>((as', []), fs', [])r'"
    using comp_split[OF assms(5)[unfolded knft_split(3)]]
    by auto
  have "length v' \<le> length es'"
    using assms(7) sminv_ge_zero[of n] minv_Suc_ge_sminv_os[of n]
    by (auto simp: es_def(2) sminv_Suc)
  then have "length cs \<le> length v"
    using arg_cong[OF es_def(1), of length] knft_split(5)
    by auto
  then obtain cs'' where cs'_split: "cs' = cs'' @ v'"
    using split_app'[OF trans[OF es_def(1) knft_split(4), symmetric]]
    by auto
  have v_def: "v = cs @ cs''"
    using trans[OF es_def(1) knft_split(4)]
    by (auto simp: cs'_split)
  have comp_init_r'': "init\<leadsto>((u0 @ as, as'), (v0 @ cs) @ cs'' @ fs, fs')r''"
    using comp_trans[OF assms(4) tdfa_split(2)]
    by (auto simp: knft_split(3) tdfa_split(1) v_def)
  have knft_comp_s''_s': "knft.computation s'' (as', (cs'' @ fs) @ fs') s'"
    using knft_split(2)
    by (auto simp: cs'_split tdfa_split(1))
  note knft_comps = knft.comp_trans[OF assms(1) knft_split(1)]
  have len_fs': "length fs' \<le> minv 0"
    using assms(7)
    by (auto simp: tdfa_split(1))
  have sminv_le: "sminv n \<le> length ((cs'' @ fs) @ fs')"
  proof -
    have "sminv n = length es'"
      using es_def(2)
      by auto
    moreover have "\<dots> \<le> length cs'"
      using arg_cong[OF knft_split(4), of length] knft_split(5)
      by auto
    moreover have "\<dots> = length ((cs'' @ fs) @ fs')"
      by (auto simp: cs'_split tdfa_split(1))
    ultimately show ?thesis
      by simp
  qed
  have sminv_ge: "length ((cs'' @ fs) @ fs') \<le> sminv n + knft.output_speed"
  proof -
    have "length ((cs'' @ fs) @ fs') = length cs'"
      by (auto simp: cs'_split tdfa_split(1))
    moreover have "\<dots> \<le> sminv n + knft.output_speed"
      using arg_cong[OF knft_split(4), of length] knft_split(5,6) sminv_Suc_ge_os[of n]
      by (simp add: es_def(2))
    finally show ?thesis .
  qed
  obtain u'' v'' ws where conflict: "length ws = n" "knft.computation s'' (u'', v'') s'"
    "length v'' \<le> length ((cs'' @ fs) @ fs')"
    "distinct (map (\<lambda>(cv, cw, r, r'). length (cv @ cw)) ws)" "(\<forall>(cv, cw, r, r')\<in>set ws.
       init\<leadsto>((u0 @ as, u''), (v0 @ cs) @ cv, cw)r \<and> r\<leadsto>((u'', []), cw, [])r' \<and> accept r' \<and>
       length v'' < length (cv @ cw))"
    using conflict_rec[OF knft_comps knft_comp_s''_s' assms(3) comp_init_r'' tdfa_split(3) assms(6)
      len_fs' sminv_le sminv_ge]
    by fast
  define ws' where "ws' = map (\<lambda>(cv, cw, r, r'). (cv @ cw, r')) ws"
  have ws'_comp: "\<And>cw r'. (cw, r') \<in> set ws' \<Longrightarrow>
    init \<leadsto>((u0 @ as @ u'', []), v0 @ cs @ cw, []) r' \<and> accept r' \<and> length v'' < length cw"
    using conflict(5) comp_trans
    by (fastforce simp: ws'_def)
  have map_ws_ws': "map (\<lambda>(cv, cw, r, r'). length (cv @ cw)) ws = map (length \<circ> fst) ws'"
    by (auto simp: ws'_def in_set_zip)
  have "distinct (map fst ws')"
    using conflict(4)
    unfolding map_ws_ws'
    by (induction ws') force+
  then have distinct_v''_ws': "distinct (v'' # map fst ws')"
    by (auto dest: ws'_comp)
  have len_ws': "length ws' = n"
    using conflict(1)
    by (auto simp: ws'_def)
  have new_pair: "(u0 @ as @ u'', v0 @ cs @ v'') \<in> \<tau>"
    using knft.comp_trans[OF assms(1) knft.comp_trans[OF knft_split(1) conflict(2)]] assms(3)
    by (auto simp: knft.\<tau>_def equiv[symmetric])
  show ?thesis
    apply (rule exI[of _ "as @ u''"])
    apply (rule exI[of _ cs])
    apply (rule exI[of _ "v'' # map fst ws'"])
    using len_ws' distinct_v''_ws' ws'_comp new_pair
    by (fastforce simp: \<tau>_def)
qed

lemma bounded: "\<exists>K. knft.bounded K"
proof (rule ccontr)
  (* home stretch *)
  define h where "h = (knft.sg + 1) * (card Q + 1)"
  (* trail length *)
  define t where "t = sminv kv"
  assume "\<not>(\<exists>K. knft.bounded K)"
  then obtain q q' u v w where unbounded: "knft.computation ninit (u, v @ w) q"
    "knft.active q []" "knft.computation ninit (u, v) q'" "knft.active q' w"
    "length w > t"
    by (auto simp add: knft.bounded_def) (metis less_or_eq_imp_le neqE)
  note q_nQ = knft.comp_closed[OF unbounded(1) knft.init_in_Q]
  note q'_nQ = knft.comp_closed[OF unbounded(3) knft.init_in_Q]
  obtain u1 v1 nqf where ext: "knft.computation q (u1, v1) nqf" "naccept nqf"
    "length u1 \<le> knft.sg" "length v1 \<le> knft.sg * knft.output_speed"
    using knft.active_Nil_dest_sg[OF unbounded(2) q_nQ]
    by auto
  obtain u2 v2 nqf' where ext': "knft.computation q' (u2, w @ v2) nqf'" "naccept nqf'"
    "length v2 \<le> (1 + knft.sg) * knft.output_speed"
    using knft.active_dest[OF unbounded(4) q'_nQ]
    by auto
  have len_w: "h \<le> length w"
    using unbounded(5) sminv_ge_zero[of kv]
    by (auto simp: h_def t_def minv.simps(1))
  obtain v' v'' where w_def: "w = v' @ v''" "length v'' = h"
    using split_long[OF len_w]
    by auto
  have "knft.computation ninit (u @ u1, (v @ v') @ v'' @ v1) nqf"
    using knft.comp_trans[OF unbounded(1) ext(1), unfolded w_def]
    by auto
  then obtain qf where qf_def: "init \<leadsto>((u @ u1, []), ((v @ v') @ v'' @ v1, [])) qf" "accept qf"
    using ext(2) equiv
    by (fastforce simp add: knft.\<tau>_def \<tau>_def)
  have "knft.computation ninit (u @ u2, (v @ v') @ v'' @ v2) nqf'"
    using knft.comp_trans[OF unbounded(3) ext'(1), unfolded w_def]
    by auto
  then obtain qf' where qf'_def: "init \<leadsto>((u @ u2, []), ((v @ v') @ v'' @ v2, [])) qf'"
    "accept qf'"
    using ext'(2) equiv
    by (fastforce simp add: knft.\<tau>_def \<tau>_def)
  have u_not_Nil: "u \<noteq> []"
    using knft.output_speed_computation[OF unbounded(1) knft.init_in_Q]
      unbounded(5)[unfolded t_def]
    by auto
  have v''_not_Nil: "v'' \<noteq> []"
    using w_def(2)[unfolded h_def]
    by auto
  then have safe_hd_v'': "safe_hd (v'' @ v1) = safe_hd (v'' @ v2)"
    using safe_hd_app''[OF v''_not_Nil]
    by auto
  have safe_hd_u1_u2: "safe_hd (u @ u1) = safe_hd (u @ u2)"
    using safe_hd_app''[OF u_not_Nil]
    by auto
  have u_Nil_contr: "u \<noteq> [] \<or> v @ v' \<noteq> []"
    by (auto simp: u_not_Nil)
  show "False"
    using first_reaches[OF qf_def(1), OF u_Nil_contr]
  proof (rule disjE)
    assume "\<exists>ws ws' q''. v @ v' = ws @ ws' \<and> ws' \<noteq> [] \<and>
      init \<leadsto>((u, u1 @ []), ws, ws' @ (v'' @ v1) @ []) q'' \<and>
      q'' \<leadsto>((u1, []), ws' @ v'' @ v1, []) qf"
    then obtain ws ws' q'' where tail: "v @ v' = ws @ ws'"
      "init \<leadsto>((u, u1 @ []), ws, ws' @ (v'' @ v1) @ []) q''"
      "q'' \<leadsto>((u1 @ [], []), ws' @ (v'' @ v1) @ [], []) qf"
      by auto
    have le: "(length (u1 @ []) + 1) * card Q \<le> (knft.sg + 1) * card Q"
      using ext(3)
      by auto
    show "False"
      using le_trans[OF lin_bounded[OF tail(2,3) qf_def(2)] le] w_def(2)
      unfolding h_def
      by auto
  next
    assume "\<exists>ws ws' q''. u = ws @ ws' \<and> ws' \<noteq> [] \<and>
      init\<leadsto>((ws, ws' @ u1 @ []), v @ v', (v'' @ v1) @ [])q'' \<and>
      q''\<leadsto>((ws' @ u1, []), v'' @ v1, [])qf"
    then obtain ws ws' q'' where tail': "u = ws @ ws'" "ws' \<noteq> []"
      "init \<leadsto>((ws, ws' @ u1 @ []), v @ v', (v'' @ v1) @ []) q''"
      "q'' \<leadsto>((ws' @ u1, []), v'' @ v1, []) qf"
      by auto
    obtain f fs where u2_def: "u2 = f # fs"
      using knft.output_speed_computation[OF ext'(1) q'_nQ] len_w
      by (cases u2) (auto simp: h_def)
    have comp_init_q'': "init \<leadsto>((ws, ws' @ u2 @ []), v @ v', (v'' @ v2) @ []) q''"
      by (rule comp_swap_same_hd[OF tail'(3)])
         (simp add: safe_hd_app'' tail'(2) v''_not_Nil)+
    have comp_q''_qf': "q'' \<leadsto>((ws' @ f # fs, []), (v'' @ v2, [])) qf'"
      using comp_pull[OF comp_init_q''] qf'_def(1)
      by (simp add: tail'(1) u2_def)
    obtain r ds ds' where tail: "q'' \<leadsto>((ws', f # fs), (ds, ds')) r"
      "r \<leadsto>((f # fs, []), (ds', [])) qf'" "v'' @ v2 = ds @ ds'"
      using comp_split[OF comp_q''_qf']
      by auto
    note r_Q = comp_closed[OF tail(1) comp_closed[OF tail'(3) init_in_Q]]
    have comp': "knft.computation q' (f # fs, (v' @ ds) @ ds') nqf'"
      using ext'(1)[unfolded w_def u2_def, simplified] tail(3)
      by auto
    have len_ds': "length ds' \<le> minv 0"
      using arg_cong[OF tail(3), of length] w_def(2) ext'(3)
      by (auto simp: minv.simps h_def)
    have comp_init_r: "init\<leadsto>((u, f # fs), v @ v' @ ds, ds')r"
      using comp_trans[OF comp_init_q'' tail(1)]
      by (auto simp: tail'(1) u2_def tail(3))
    have len_v': "sminv kv \<le> length ((v' @ ds) @ ds')"
      using unbounded(5)
      by (auto simp: tail(3)[symmetric] w_def(1) t_def)
    obtain u'' v'' ws where conflict:
      "length ws = Suc kv" "distinct ws" "\<And>cw. cw\<in>set ws \<Longrightarrow> (u @ u'', v @ v'' @ cw) \<in> \<tau>"
      using conflict[OF unbounded(3) comp' ext'(2) comp_init_r tail(2) qf'_def(2) len_ds' len_v']
      by auto
    have sub: "(\<lambda>w. v @ v'' @ w) ` set ws \<subseteq> {bs. (u @ u'', bs) \<in> \<tau>}"
      using conflict(3)
      by auto
    have "card ((\<lambda>w. v @ v'' @ w) ` set ws) = card (set ws)"
      by (rule card_image) (auto simp: inj_on_def)
    moreover have "\<dots> = Suc kv"
      using distinct_card[OF conflict(2)]
      by (auto simp: conflict(1))
    finally show "False"
      using sub kval[of "u @ u''"]
      by (metis card_mono not_less_eq_eq)
  qed
qed

end

locale necessary = knft: kNFT ninit n\<delta> naccept nQ + kTDFA init \<delta> accept Q
  for ninit :: "'s"
  and n\<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> 'b list \<Rightarrow> bool"
  and naccept :: "'s \<Rightarrow> bool"
  and nQ :: "'s set"
  and init :: "'t"
  and \<delta> :: "'t \<Rightarrow> 'a Al \<times> 'b Al \<Rightarrow> ('t \<times> bool \<times> bool) option"
  and accept :: "'t \<Rightarrow> bool"
  and Q :: "'t set" +
assumes equiv: "knft.\<tau> = \<tau>"
begin

interpretation otdfa: oTDFA otdfa_init otdfa_delta otdfa_accept otdfa_Q
  using otdfa_finite_Q otdfa_init_in_Q otdfa_closed[rotated]
        otdfa_move_left otdfa_move_right otdfa_no_step otdfa_move_one
  by unfold_locales auto

interpretation nec: necessary' kv ninit n\<delta> naccept nQ otdfa_init otdfa_delta otdfa_accept otdfa_Q
  using kval tdfa_equiv_otdfa
  by unfold_locales (auto simp add: equiv tdfa_equiv_otdfa)

(* Theorem 10 *)

lemma bounded: "\<exists>K. knft.bounded K"
  using nec.bounded .

end

end