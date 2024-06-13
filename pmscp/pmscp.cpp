#include "pmscp.h"

#include <random>
#include <iostream>
#include <time.h>
#include <algorithm>
#include <chrono>

#define INF 0x3fffffff

using namespace std;

namespace pmscp {
	class Solver {

		// random number generator.
		mt19937 pseudoRandNumGen;
		void initRand(int seed) { pseudoRandNumGen = mt19937(seed); }
		int fastRand(int lb, int ub) { return (pseudoRandNumGen() % (ub - lb)) + lb; }
		int fastRand(int ub) { return pseudoRandNumGen() % ub; }
		int rand(int lb, int ub) { return uniform_int_distribution<int>(lb, ub - 1)(pseudoRandNumGen); }
		int rand(int ub) { return uniform_int_distribution<int>(0, ub - 1)(pseudoRandNumGen); }
	
	public:
		double calProfit(Sets X, PSetCovering psc) {
			double res = 0;
			vector<int> set2G(psc.setNum);
			for (int gid = 0; gid < psc.groupNum; ++gid) {
				for (auto tmps = psc.group[gid].begin(); tmps != psc.group[gid].end(); ++tmps) {
					set2G[psc.SMap[*tmps]] = gid;
				}
			}
			vector<int> use_e(psc.elemNum, 0), use_g(psc.groupNum, 0);
			for (auto tmpS = X.begin(); tmpS != X.end(); ++tmpS) {
				int idx = psc.SMap[*tmpS];
				int gid = set2G[*tmpS];
				res -= psc.SCost[idx];
				if (use_g[gid] == 0) {
					res -= psc.GCost;
					use_g[gid] = 1;
				}

				for (auto Eid = psc.coveringSet[idx].begin(); Eid != psc.coveringSet[idx].end(); ++Eid) {
					if (use_e[*Eid] == 0) {
						res += psc.profit[*Eid];
						use_e[*Eid] = 1;
					}
				}
			}
			return res;
		}
		bool testDelta(Sets X, PSetCovering psc, vector<double> delta) {
			vector<double> testDel(psc.setNum);
			vector<int> visE(psc.elemNum, 0);
			vector<int> visG(psc.groupNum, 0);
			vector<int> set2G(psc.setNum);
			for (int gid = 0; gid < psc.groupNum; ++gid) {
				for (auto tmps = psc.group[gid].begin(); tmps != psc.group[gid].end(); ++tmps) {
					set2G[psc.SMap[*tmps]] = gid;
				}
			}

			for (auto s = X.begin(); s != X.end(); ++s) {
				int idx = psc.SMap[*s];
				visG[set2G[idx]] += 1;
				for (auto e = psc.coveringSet[idx].begin(); e != psc.coveringSet[idx].end(); ++e) {
					visE[*e] += 1;
				}
			}

			for (auto setN = psc.SMap.begin(); setN != psc.SMap.end(); ++setN) {
				SetId sid = (*setN).first;
				int idx = (*setN).second;
				// 当前覆盖集位于初始解中
				if (X.find(sid) != X.end()) {
					for (auto eid = psc.coveringSet[idx].begin(); eid != psc.coveringSet[idx].end(); ++eid) {
						if (visE[*eid] == 1) testDel[idx] -= psc.profit[*eid];
					}
					testDel[idx] += psc.SCost[idx];
					if (visG[set2G[idx]] == 1) testDel[idx] += psc.GCost;
				}
				else { //当前覆盖集不在初始解中
					for (auto eid = psc.coveringSet[idx].begin(); eid != psc.coveringSet[idx].end(); ++eid) {
						if (visE[*eid] == 0) testDel[idx] += psc.profit[*eid];
					}
					testDel[idx] -= psc.SCost[idx];
					if (visG[set2G[idx]] == 0) testDel[idx] -= psc.GCost;
				}
			}
			for (auto setN = psc.SMap.begin(); setN != psc.SMap.end(); ++setN) {
				SetId sid = (*setN).first;
				int idx = (*setN).second;
				if (delta[idx] - testDel[idx] <= 0.00001 && delta[idx] - testDel[idx] >= -0.00001) continue;
				else {
					cerr << "当前delta的增量计算有问题!" << endl;
					return false;
				}
			}
			return true;
		}
		// 化简部分需要重写
		PSetCovering Reduction(PSetCovering psc) {
			//进行规约操作后，setNum、coveringSet、gourp、SCost都可能相应发生改变
			int new_setNum = psc.setNum;

			// 首先确定要被删除的覆盖集
			vector<int> delSets;
			for (int sid = 0; sid < psc.setNum; ++sid) {
				int pft = 0;
				for (auto eid = psc.coveringSet[sid].begin(); eid != psc.coveringSet[sid].end(); ++eid) {
					pft += psc.profit[*eid];
				}
				pft -= psc.SCost[sid];
				if (pft <= 0) delSets.push_back(sid);
			}

			// 依次删除这些覆盖集
			for (int i = 0; i < delSets.size(); ++i) {
				SetId dset = delSets[i];
				psc.SMap.erase(dset);
				new_setNum -= 1;
				
				for (int gid = 0; gid < psc.groupNum; ++gid) {
					if (psc.group[gid].find(dset) != psc.group[gid].end()) {
						psc.group[gid].erase(dset);
					}
				}
			}
			return psc;
		}

		double solve(Sets& X, PSetCovering& psc, function<long long()> restMilliSec, int seed) {
			initRand(seed);
			double epsilon = 0.6; //ε表示贪心选择的概率
			int omega = 300, beta = 1000; // ω表示局部搜索的迭代轮次；β表示禁忌搜索的深度
			// 首先对覆盖集进行化简
			PSetCovering new_psc = Reduction(psc);

			Sets best_X, X0;
			double best_f = 0; //记录最高的收益
			vector<double> eta(new_psc.setNum, 0.5); //η表示初始化的历史信息向量
			vector<double> gamma(2, 0.5); //γ表示扰动概率的向量
			vector<int> visE(new_psc.elemNum, 0); //确定e被解中的几个集合覆盖
			vector<int> visG(new_psc.groupNum, 0); //确定解中有多少集合属于同一个组
			vector<double> delta(new_psc.setNum, 0); //快速评估邻域解的质量
			vector<int> set2G(new_psc.setNum); //确定覆盖集属于哪个组
			vector<unordered_set<SetId>> e2Set(new_psc.elemNum); //确定element由哪些覆盖集所覆盖
			double d0 = 50, d1 = 0, d2 = 0; //确定扰动的选择

			for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
				SetId sid = (*setN).first;
				int idx = (*setN).second;
				for (auto e = new_psc.coveringSet[idx].begin(); e != new_psc.coveringSet[idx].end(); ++e)
					e2Set[*e].insert(sid);
			}
			for (int gid = 0; gid < new_psc.groupNum; ++gid) {
				for (auto tmps = new_psc.group[gid].begin(); tmps != new_psc.group[gid].end(); ++tmps) {
					set2G[*tmps] = gid;
				}
			}

			auto LearningDrivenInitialization = [&]() { //使用 psc; epsilon; eta三个变量
				Sets tmpX;
				unordered_set<SetId> tmpS;
				vector<int> tmpVisE(new_psc.elemNum, 0);
				
				for (int i = 0; i < new_psc.setNum; ++i)
					if (new_psc.SMap.find(i) != new_psc.SMap.end()) 
						tmpS.insert(new_psc.SMap[i]);

				while (tmpS.size() > 0) {
					SetId sid;
					double rNum = fastRand(10000) / 10000.0;
					if (rNum < epsilon) {
						// 这是一个可能改进的地方, 使用堆会提高性能
						// 做一些修改
						double maxP = 0;
						for (auto inflect = tmpS.begin(); inflect != tmpS.end(); ++inflect) {
							SetId sid1 = (*inflect);
							int idx = new_psc.SMap[sid1];
							if (maxP < eta[idx]) {
								maxP = eta[idx];
								sid = sid1;
							}
						}
					}
					else {
						auto it = next(tmpS.begin(), fastRand(tmpS.size()));
						sid = *it;
					}
					tmpS.erase(sid);

					double gainCnt = 0;
					int idx = new_psc.SMap[sid];
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						if (tmpVisE[*eid] == 0)
							gainCnt += new_psc.profit[*eid];	 
					}
					rNum = fastRand(10000) / 10000.0;
					if (gainCnt - new_psc.SCost[idx] > 0 && rNum < eta[idx]) {
						tmpX.insert(sid);
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) 
							tmpVisE[*eid] = 1;
					} 
				}
				return tmpX;
			};

			auto flip = [&](Sets& X1, SetId bestSet) {
				int idx = new_psc.SMap[bestSet];
				// 调整自己的delta
				delta[idx] = -delta[idx];
				// 根据group调整delta
				int curG = set2G[idx];
				bool BexistX = X1.find(bestSet) != X1.end();
				for (auto s = new_psc.group[curG].begin(); s != new_psc.group[curG].end(); ++s) {
					if (*s == bestSet) continue;
					bool tmpeX = X1.find(*s) != X1.end();
					if (tmpeX && BexistX && visG[curG] == 2 || visG[curG] == 0) delta[new_psc.SMap[*s]] += new_psc.GCost;
					else if (BexistX && (!tmpeX) && visG[curG] == 1 || (!BexistX) && tmpeX && visG[curG] == 1)
						delta[new_psc.SMap[*s]] -= new_psc.GCost;
				}

				// 根据element调整delta
				for (auto e = new_psc.coveringSet[idx].begin(); e != new_psc.coveringSet[idx].end(); ++e) {
					for (auto s = e2Set[*e].begin(); s != e2Set[*e].end(); ++s) {
						if (*s == bestSet) continue;
						bool tmpeX = X1.find(*s) != X1.end();
						if (tmpeX && BexistX && visE[*e] == 2 || visE[*e] == 0) delta[new_psc.SMap[*s]] -= new_psc.profit[*e];
						else if (BexistX && (!tmpeX) && visE[*e] == 1 || (!BexistX) && tmpeX && visE[*e] == 1)
							delta[new_psc.SMap[*s]] += new_psc.profit[*e];
					}
				}

				//更改X1
				if (X1.find(bestSet) != X1.end()) { //在当前解中，移出去
					X1.erase(bestSet);
					visG[curG] -= 1;
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						visE[*eid] -= 1;
					}
				}
				else { //不在当前解中，移进来
					X1.insert(bestSet);
					visG[curG] += 1;
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						visE[*eid] += 1;
					}
				}
			};

			auto FlipTabuSearch = [&](Sets& X1, double& f_X1) {
				// 禁忌表的设计/delta的计算
				vector<int> tabuList(new_psc.setNum, 0);
				int iterCnt = 0, non_improve = 0; //记录迭代轮次和未改进次数
				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<int> tmpvise = visE;
				vector<int> tmpvisg = visG;
				while (non_improve < beta && restMilliSec() > 0) {
					iterCnt += 1;
					int bestSet;
					double maxProfit = -1e8;
					// 这里确定禁忌表和特赦准则的问题
					for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
						SetId sid = (*setN).first;
						int idx = (*setN).second;
						if (delta[idx] > maxProfit && (tabuList[idx] < iterCnt || fb < f_X1 + delta[idx])) {
							maxProfit = delta[idx];
							bestSet = sid;
						}
					}

					if (maxProfit == -1e8) continue;
					f_X1 = f_X1 + maxProfit;

					// 调整δ, 更改X1和TabuList
					flip(X1, bestSet);

					if (X1.find(bestSet) != X1.end())
						tabuList[bestSet] = iterCnt + fastRand(1, 6); //这个禁忌值偏大了？
					else tabuList[bestSet] = iterCnt + new_psc.SMap.size();
					
					if (fb - f_X1 < 0.0001 && fb - f_X1 > -0.0001 || fb > f_X1) {
						non_improve += 1;
					}
					else {
						Xb = X1;
						fb = f_X1;
						tmpDel = delta;
						tmpvise = visE;
						tmpvisg = visG;
						non_improve = 0;
					}
				}
				X1 = Xb;
				f_X1 = fb;
				delta = tmpDel;
				visG = tmpvisg;
				visE = tmpvise;
			};

			// 需要一个禁忌操作吗？
			auto SwapDescentSearch = [&](Sets& X1, double& f_X1) {
				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<int> tmpvise = visE;
				vector<int> tmpvisg = visG;
				Sets Nx1;

				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN).first;
					if (X1.find(sid) != X1.end()) continue;
					Nx1.insert(sid);
				}

				int non_improve = 0;
				int iter_cnt = 0;
				while (non_improve == 0 && restMilliSec() > 0) {
					iter_cnt += 1;
					non_improve = 1;
					int bestS1, bestS2;
					double bestdp = -1e8;
					//选择最佳邻域动作
					for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
						int idx1 = new_psc.SMap[*s1];
						double dp1 = delta[idx1];
						// flip(s1, X1, Nx1) ->delta
						
						int s2;
						for (auto tmps = Nx1.begin(); tmps != Nx1.end(); ++tmps) {
							int curg = set2G[idx1];
							int idx2 = new_psc.SMap[*tmps];
							double dpn = delta[idx2];
							if (visG[curg] == 1 && set2G[idx2] == curg)
								dpn -= new_psc.GCost;

							for (auto e = new_psc.coveringSet[idx1].begin(); e != new_psc.coveringSet[idx1].end(); ++e) {
								if (visE[*e] == 1 && e2Set[*e].find(*tmps) != e2Set[*e].end())
									dpn += new_psc.profit[*e];
							}
							
							double dsum = dp1 + dpn;
							if (dsum > bestdp) {
								bestS1 = *s1;
								bestS2 = *tmps;
								bestdp = dsum;
							}
						}
					}
					Nx1.insert(bestS1);
					Nx1.erase(bestS2);
					// 以上动作执行完后，确定 s1，s2为最佳邻域动作，执行这些动作并修改相应的值即可
					//f_X1 += delta[bestS1];
					flip(X1, bestS1);
					//f_X1 += delta[bestS2];
					flip(X1, bestS2);
					f_X1 += bestdp;

					if (fb < f_X1) {
						Xb = X1;
						fb = f_X1;

						tmpDel = delta;
						tmpvise = visE;
						tmpvisg = visG;
						non_improve = 0;
					}
				}
				X1 = Xb;
				f_X1 = fb;
				delta = tmpDel;
				visG = tmpvisg;
				visE = tmpvise;
			};

			auto TwoPhaseLS = [&](Sets& X1, double& f_X1) {
				/*auto start1 = std::chrono::high_resolution_clock::now();*/

				Sets Xb = X1;
				double f_b = f_X1;
				int non_improve = 0;
				vector<double> tmpDel = delta;
				vector<int> tmpvise = visE;
				vector<int> tmpvisG = visG;
				int iter_cnt = 0;
				while (non_improve == 0 && restMilliSec() > 0) {
					iter_cnt += 1;
					non_improve = 1;
					FlipTabuSearch(X1, f_X1);
					/*cerr << "after exe Tabu" << endl;
					bool testDel1 = testDelta(X1, new_psc, delta);*/
					SwapDescentSearch(X1, f_X1);
					//cerr << "after exe Swap" << endl;
					//bool testDel2 = testDelta(X1, new_psc, delta);

					if (f_X1 > f_b) {
						f_b = f_X1;
						Xb = X1;
						tmpvise = visE;
						tmpvisG = visG;
						tmpDel = delta;
						non_improve = 0;
					}
				}
				f_X1 = f_b;
				X1 = Xb;
				delta = tmpDel;
				visE = tmpvise;
				visG = tmpvisG;

				/*cerr << "TwoPhaseLS 执行次数: " << iter_cnt << endl;
				auto end1 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed = end1 - start1;
				std::cout << "Elapsed time: " << elapsed.count() / 1000.0 << " s" << std::endl;*/
			};

			auto Perturbation = [&](Sets& tmpX, int& t_type, double& f_tmpX) {
				if (fastRand(10000) / 10000.0 < gamma[0]) {
					// 执行Set_Pertubation
					t_type = 0;
					Sets tmpX2 = tmpX;
					vector<int> Ns;
					/*for (int s = 0; s < new_psc.setNum; ++s) 
						if (tmpX.find(s) == tmpX.end()) Ns.push_back(s);*/
					for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
						SetId sid = (*setN).first;
						if (tmpX.find(sid) == tmpX.end()) Ns.push_back(sid);
					}

					int len = Ns.size();
					for (auto s = tmpX2.begin(); s != tmpX2.end(); ++s) {
						int j = new_psc.SMap[*s];
						if (len == 0) break;
						bool isDel = fastRand(10000) / 10000.0 < 0.3;
						if (isDel) {
							//tmpX.erase(*s);
							f_tmpX += delta[j];
							flip(tmpX, *s);
							int idx = fastRand(len);
							//tmpX.insert(Ns[idx]);
							SetId sid = Ns[idx];
							int sidx = new_psc.SMap[sid];
							f_tmpX += delta[sidx];
							flip(tmpX, sid);
							Ns[idx] = Ns[len - 1];
							Ns.pop_back();
							len -= 1;
						}
					}
				}
				else {
					// 执行Group_Pertubation
					t_type = 1;
					Sets tmpX2 = tmpX;
					vector<int> Z, Nz; //Z表示 组中的覆盖集与X的交集不为空的组序号
					double p = 0.3;
					for (int g = 0; g < new_psc.groupNum; g++) {
						if (visG[g] >= 1) Z.push_back(g);
						else Nz.push_back(g);
					}
					int Zlen = Z.size();
					int tochs = max(int(p * Zlen), 1);
					for (int i = 0; i < tochs; ++i) {
						int len = Z.size();
						if (len == 0) break;
						int idx = fastRand(len);
						int cg = Z[idx]; // cg为选出的组
						Z[idx] = Z[len - 1];
						Z.pop_back();
						for (auto s = new_psc.group[cg].begin(); s != new_psc.group[cg].end(); ++s) {
							if (tmpX2.find(*s) != tmpX2.end()) {
								//tmpX.erase(*s);
								f_tmpX += delta[new_psc.SMap[*s]];
								flip(tmpX, *s);
							} 
						}
					}

					for (int i = 0; i < tochs; ++i) {
						int len = Nz.size();
						if (Nz.size() == 0) {
							//cerr << "扰动部分的问题! " << endl;
							break;
						}
						int idx = fastRand(len);
						int cg = Nz[idx];
						Nz[idx] = Nz[len - 1];
						Nz.pop_back();

						int fcnt = tmpX2.size() / Zlen;
						auto tmpg = new_psc.group[cg];
						for (int j = 0; j < fcnt; ++j) {
							int idx = fastRand(tmpg.size());
							auto it = next(tmpg.begin(), idx);
							SetId s = *it;
							tmpg.erase(s);
							/*tmpX.insert(s);*/
							f_tmpX += delta[new_psc.SMap[s]];
							flip(tmpX, s);
						}
					}
				}
			};

			auto IntensifivationDrivenILS = [&](Sets input, double& f_X0) {
				auto start = std::chrono::high_resolution_clock::now();

				Sets tmpX = input, Xp = input;
				double tmp_f = f_X0, fp = f_X0;
				int non_improve = 0;
				int t_type = -1;
				int iter_cnt = 0;
				double tmpr = 0;
				vector<double> tmpDel = delta;
				vector<int> tmpvise = visE;
				vector<int> tmpvisG = visG;
				while (non_improve < omega && restMilliSec() > 0) {
					iter_cnt += 1;
					TwoPhaseLS(Xp, fp);
					if (fp - tmp_f >= -0.0001 && fp - tmp_f <= 0.0001) non_improve += 1;
					else if (fp < tmp_f) non_improve += 1;
					else {
						// 更新γ
						if (t_type == 0) d1 += 1;
						else if (t_type == 1) d2 += 1;
						gamma[0] = (d0 + d1) / (2 * d0 + d1 + d2);
						gamma[1] = 1 - gamma[0];

						// 更新eta
						for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
							int j = (*setN).second;
							SetId sid = (*setN).first;
							double phi1 = 0.2, phi2 = 0.3, phi3 = 0.3; 
							double alpha = 0.95;
							bool existX0 = Xp.find(sid) != Xp.end(), existBX = tmpX.find(sid) != tmpX.end();
							if (existX0 && existBX) eta[j] = phi1 + (1 - phi1) * eta[j];
							else if (existX0 && (!existBX)) eta[j] = phi2 + (1 - phi2) * eta[j];
							else if ((!existX0) && (!existBX)) eta[j] = (1 - phi1) * eta[j];
							else eta[j] = (1 - phi2) * eta[j];
							// 进行平滑操作
							if (eta[j] > alpha) eta[j] = (1 - phi3) * eta[j];
							else if (eta[j] < 1 - alpha) eta[j] = phi3 + (1 - phi3) * eta[j];
						
						}

						tmpX = Xp;
						tmp_f = fp;
						tmpDel = delta;
						tmpvise = visE;
						tmpvisG = visG;
						non_improve = 0; 
						cerr << "当前最好结果为: " << tmp_f << endl;
					}
					
					Xp = tmpX;
					fp = tmp_f;
					visE = tmpvise;
					visG = tmpvisG;
					delta = tmpDel;
					Perturbation(Xp, t_type, fp);
				}
				cerr << "IntensifivationDrivenILS 执行次数: " << iter_cnt << endl;
				f_X0 = tmp_f;

				auto end = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed = end - start;
				std::cout << "Elapsed time: " << elapsed.count() / 1000.0 << " s" << std::endl;
				return tmpX;
			};

			while (restMilliSec() > 0) {
				// 获得初始解后，要确定δ向量和初始解的收益值，即f_X0
				double f_X0 = 0;
				X0 = LearningDrivenInitialization();
				// 计算收益值
				f_X0 = calProfit(X0, new_psc);
				// 计算δ函数 和visG、visE
				fill(visG.begin(), visG.end(), 0);
				fill(visE.begin(), visE.end(), 0);
				fill(delta.begin(), delta.end(), 0);
				for (auto s = X0.begin(); s != X0.end(); ++s) {
					visG[set2G[*s]] += 1;
					for (auto eid = new_psc.coveringSet[*s].begin(); eid != new_psc.coveringSet[*s].end(); ++eid)
						visE[*eid] += 1;
				}
				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN).first;
					int idx = (*setN).second;
					// 当前覆盖集位于初始解中
					if (X0.find(sid) != X0.end()) {
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
							if (visE[*eid] == 1) delta[idx] -= new_psc.profit[*eid];
						}
						delta[idx] += new_psc.SCost[idx];
						if (visG[set2G[idx]] == 1) delta[idx] += new_psc.GCost;
					}
					else { //当前覆盖集不在初始解中
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
							if (visE[*eid] == 0) delta[idx] += new_psc.profit[*eid];
						}
						delta[idx] -= new_psc.SCost[idx];
						if (visG[set2G[idx]] == 0) delta[idx] -= new_psc.GCost;
					}
				}
				
				cerr << "IFD执行前的收益值为：" << f_X0 << endl;
				X0 = IntensifivationDrivenILS(X0, f_X0);
				double testf = calProfit(X0, new_psc);
				if (testf - f_X0 >= 0.00001 || testf - f_X0 <= -0.00001) {
					cerr << "增量计算有问题！" << endl;
					cerr << "realf :" << testf << " f_X0: " << f_X0 << endl;
				}
				
				// 确定当前解与之前得到的解的相似度
				int sameCnt = 0;
				for (auto s = X0.begin(); s != X0.end(); ++s) {
					if (best_X.find(*s) != best_X.end()) sameCnt += 1;
				}
				cerr << "局部最优解的相似度为：" << sameCnt / (double)best_X.size() << endl;
				
				if (f_X0 > best_f) {
					best_X = X0;
					best_f = f_X0;
				} 
				cerr << "当前解的大小为：" << best_X.size() << endl;
				cerr << "当前最大收益值为：" << best_f << endl << endl;
			}
			double real_f = calProfit(best_X, new_psc);
			cerr << "真实最大收益值为：" << real_f << endl;
			cerr << "增量计算的收益值为: " << best_f << endl;
			return best_f;
		}
	};

	double solvePMForSetCovering(Sets& output, PSetCovering& input, std::function<long long()> restMilliSec, int seed) {
		return Solver().solve(output, input, restMilliSec, seed);
	}
}