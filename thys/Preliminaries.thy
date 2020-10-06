theory Preliminaries
  imports Computation
begin

context NFT
begin

definition "bv' t \<longleftrightarrow> (\<forall>f1 f2 q1 q2 a b1 b2 v1 v2 w1 w2.
  accept f1 \<and> accept f2 \<and> q1 \<in> Q \<and> q2 \<in> Q \<and>
  init \<leadsto>(a, v1) q1 \<and> q1 \<leadsto>(b1, w1) f1 \<and>
  init \<leadsto>(a, v2) q2 \<and> q2 \<leadsto>(b2, w2) f2 \<longrightarrow> lcp_dist v1 v2 \<le> t)"

(* Lemma 7 *)

lemma bv_prop: "(\<forall>k. \<exists>t. bv k t) \<longleftrightarrow> (\<exists>t. bv' t)"
proof (rule iffI)
  assume "\<forall>k. \<exists>t. bv k t"
  then obtain t where t_def:
    "\<And>f1 f2 q1 q2 a b1 b2 u v1 v2 w1 w2. accept f1 \<Longrightarrow> accept f2 \<Longrightarrow> q1 \<in> Q \<Longrightarrow> q2 \<in> Q \<Longrightarrow>
      init \<leadsto>(a, u @ v1) q1 \<Longrightarrow> q1 \<leadsto>(b1, w1) f1 \<Longrightarrow>
      init \<leadsto>(a, u @ v2) q2 \<Longrightarrow> q2 \<leadsto>(b2, w2) f2 \<Longrightarrow>
      length b1 + length b2 \<le> sg + sg \<Longrightarrow> lcp_dist (v1 @ w1) (v2 @ w2) \<le> t"
    unfolding bv_def
    by metis
  {
    fix k
    fix f1 f2 q1 q2 a b1 b2 v1 v2 w1 w2
    assume assms: "accept f1" "accept f2" "q1 \<in> Q" "q2 \<in> Q"
      "init \<leadsto>(a, [] @ v1) q1" "q1 \<leadsto>(b1, w1) f1"
      "init \<leadsto>(a, [] @ v2) q2" "q2 \<leadsto>(b2, w2) f2"
    obtain b1' w1' f1' where sg1: "q1 \<leadsto>(b1', w1') f1'" "accept f1'" "length b1' \<le> sg"
      using active_Nil_dest_sg[OF _ assms(3)] assms(1,6)
      by (auto simp: active_def)
    obtain b2' w2' f2' where sg2: "q2 \<leadsto>(b2', w2') f2'" "accept f2'" "length b2' \<le> sg"
      using active_Nil_dest_sg[OF _ assms(4)] assms(2,8)
      by (auto simp: active_def)
    have "lcp_dist (v1 @ w1') (v2 @ w2') \<le> t"
      using t_def[OF sg1(2) sg2(2) assms(3,4,5) sg1(1) assms(7) sg2(1)] sg1(3) sg2(3)
      by auto
    then have "lcp_dist v1 v2 \<le> t + length w1' + length w2'"
      using lcp_dist_le_app_sum[of v1 v2 w1' w2']
      by auto
    also have "\<dots> \<le> t + length b1' * output_speed + length b2' * output_speed"
      using output_speed_computation[OF sg1(1) assms(3)]
        output_speed_computation[OF sg2(1) assms(4)]
      by auto
    also have "\<dots> \<le> t + sg * output_speed + sg * output_speed"
      using sg1(3) sg2(3)
      by (auto simp add: add_mono)
    finally have "lcp_dist v1 v2 \<le> t + sg * output_speed + sg * output_speed" .
  }
  then show "\<exists>t. bv' t"
    unfolding bv'_def
    by auto blast
next
  assume "\<exists>t. bv' t"
  then obtain t where t_def:
    "\<And>f1 f2 q1 q2 a b1 b2 v1 v2 w1 w2. accept f1 \<Longrightarrow> accept f2 \<Longrightarrow> q1 \<in> Q \<Longrightarrow> q2 \<in> Q \<Longrightarrow>
      init \<leadsto>(a, v1) q1 \<Longrightarrow> q1 \<leadsto>(b1, w1) f1 \<Longrightarrow>
      init \<leadsto>(a, v2) q2 \<Longrightarrow> q2 \<leadsto>(b2, w2) f2 \<Longrightarrow> lcp_dist v1 v2 \<le> t"
    unfolding bv'_def
    by metis
  {
    fix k
    fix f1 f2 q1 q2 a b1 b2 u v1 v2 w1 w2
    assume assms: "accept f1" "accept f2" "q1 \<in> Q" "q2 \<in> Q"
      "init \<leadsto>(a, u @ v1) q1" "q1 \<leadsto>(b1, w1) f1"
      "init \<leadsto>(a, u @ v2) q2" "q2 \<leadsto>(b2, w2) f2"
      "length b1 + length b2 \<le> k"
    have "lcp_dist (v1 @ w1) (v2 @ w2) \<le> t + length b1 * output_speed + length b2 * output_speed"
      using lcp_dist_app_le_sum[of v1 w1 v2 w2] t_def[OF assms(1,2,3,4,5,6,7,8)]
        output_speed_computation[OF assms(6,3)] output_speed_computation[OF assms(8,4)]
      unfolding lcp_dist_same_pref
      by auto
    also have "\<dots> \<le> t + k * output_speed"
      using assms(9)
      by auto (metis add_mult_distrib mult_le_mono1)
    finally have "lcp_dist (v1 @ w1) (v2 @ w2) \<le> t + k * output_speed" .
  }
  then show "\<forall>k. \<exists>t. bv k t"
    unfolding bv_def
    by blast
qed

lemma bv'_bounded:
  assumes "bv' t"
  shows "bounded t"
proof -
  have bv': "\<And>f1 f2 q1 q2 a b1 b2 v1 v2 w1 w2. accept f1 \<Longrightarrow> accept f2 \<Longrightarrow> q1 \<in> Q \<Longrightarrow> q2 \<in> Q \<Longrightarrow>
    init \<leadsto>(a, v1) q1 \<Longrightarrow> q1 \<leadsto>(b1, w1) f1 \<Longrightarrow>
    init \<leadsto>(a, v2) q2 \<Longrightarrow> q2 \<leadsto>(b2, w2) f2 \<Longrightarrow> lcp_dist v1 v2 \<le> t"
    using assms
    by (fastforce simp: bv'_def)
  {
    fix q q' u v v'
    assume prems: "init \<leadsto>(u, v @ v') q" "active q []"
      "init \<leadsto>(u, v) q'" "active q' v'"
    obtain r as bs where tail: "q \<leadsto>(as, bs) r" "accept r"
      using prems(2)
      by (auto simp: active_def)
    obtain r' as' bs' where tail': "q' \<leadsto>(as', v' @ bs') r'" "accept r'"
      using prems(4)
      by (auto simp: active_def)
    note q_Q = comp_closed[OF prems(1) init_in_Q]
    note q'_Q = comp_closed[OF prems(3) init_in_Q]
    have "lcp_dist (v @ v') v = lcp_dist (v @ v') (v @ [])"
      by auto
    moreover have "\<dots> = length v'"
      unfolding lcp_dist_same_pref
      by simp
    finally have "length v' \<le> t"
      using bv'[OF tail(2) tail'(2) q_Q q'_Q prems(1) tail(1) prems(3) tail'(1)]
      by auto
  }
  then show ?thesis
    by (auto simp: bounded_def)
qed

end

end