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
				// ��ǰ���Ǽ�λ�ڳ�ʼ����
				if (X.find(sid) != X.end()) {
					for (auto eid = psc.coveringSet[idx].begin(); eid != psc.coveringSet[idx].end(); ++eid) {
						if (visE[*eid] == 1) testDel[idx] -= psc.profit[*eid];
					}
					testDel[idx] += psc.SCost[idx];
					if (visG[set2G[idx]] == 1) testDel[idx] += psc.GCost;
				}
				else { //��ǰ���Ǽ����ڳ�ʼ����
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
					cerr << "��ǰdelta����������������!" << endl;
					return false;
				}
			}
			return true;
		}
		PSetCovering Reduction(PSetCovering psc) {
			//���й�Լ������setNum��coveringSet��gourp��SCost��������Ӧ�����ı�
			int new_setNum = psc.setNum;

			// ����ȷ��Ҫ��ɾ���ĸ��Ǽ�
			vector<int> delSets;
			for (int sid = 0; sid < psc.setNum; ++sid) {
				double pft = 0;
				for (auto eid = psc.coveringSet[sid].begin(); eid != psc.coveringSet[sid].end(); ++eid) {
					pft += psc.profit[*eid];
				}
				if (pft <= psc.SCost[sid]) delSets.push_back(sid);
			}

			// ����ɾ����Щ���Ǽ�
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
			double epsilon = 0.6; //�ű�ʾ̰��ѡ��ĸ���
			int omega = 300, beta = 1000; // �ر�ʾ�ֲ������ĵ����ִΣ��±�ʾ�������������
			// ���ȶԸ��Ǽ����л���
			PSetCovering new_psc = Reduction(psc);
			//PSetCovering new_psc = psc;

			Sets best_X, X0;
			double best_f = 0; //��¼��ߵ�����
			vector<double> eta(new_psc.setNum, 0.5); //�Ǳ�ʾ��ʼ������ʷ��Ϣ����
			vector<double> gamma(2, 0.5); //�ñ�ʾ�Ŷ����ʵ�����
			vector<unordered_set<SetId>> visE(new_psc.elemNum); //ȷ��e�����е��ļ������ϸ���
			vector<unordered_set<SetId>> visG(new_psc.groupNum); //ȷ����������Щ��������ͬһ����
			vector<double> delta(new_psc.setNum, 0); //������������������
			vector<int> set2G(new_psc.setNum); //ȷ�����Ǽ������ĸ���
			vector<unordered_set<SetId>> e2Set(new_psc.elemNum); //ȷ��element����Щ���Ǽ�������
			double d0 = 50, d1 = 0, d2 = 0; //ȷ���Ŷ���ѡ��

			double times = 0, times2 = 0, times3 = 0, times4 = 0;

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

			auto LearningDrivenInitialization = [&]() { //ʹ�� psc; epsilon; eta��������
				Sets tmpX;
				unordered_set<SetId> tmpS;
				vector<int> tmpVisE(new_psc.elemNum, 0), tmpVisG(new_psc.groupNum, 0);
				
				for (auto smp = new_psc.SMap.begin(); smp != new_psc.SMap.end(); ++smp) 
					tmpS.insert((*smp).first);
				
				while (tmpS.size() > 0) {
					SetId sid;
					double rNum = fastRand(10000) / 10000.0;
					if (rNum < epsilon) {
						// ����һ�����ܸĽ��ĵط�, ʹ�öѻ��������
						// ��һЩ�޸�
						double maxP = 0;
						vector<SetId> sids;
						for (auto inflect = tmpS.begin(); inflect != tmpS.end(); ++inflect) {
							SetId sid1 = (*inflect);
							int idx = new_psc.SMap[sid1];
							if (maxP < eta[idx]) {
								sids.clear();
								maxP = eta[idx];
								//sid = sid1;
								sids.push_back(sid1);
							}
							else if (abs(maxP - eta[idx]) < 0.0001) sids.push_back(sid1);
						}
						sid = sids[fastRand(sids.size())];
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
					/*if (tmpVisG[set2G[sid]] == 0) gainCnt -= new_psc.GCost;*/
					rNum = fastRand(10000) / 10000.0;
					if (gainCnt > new_psc.SCost[idx] && rNum < eta[idx]) {
						tmpX.insert(sid);
						tmpVisG[set2G[sid]] = 1;
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) 
							tmpVisE[*eid] = 1;
					} 
				}
				return tmpX;
			};
			
			// flipҲ�����˸Ķ���������������
			auto flip = [&](Sets& X1, SetId bestSet) {
				int idx = new_psc.SMap[bestSet];
				// �����Լ���delta
				delta[idx] = -delta[idx];
				// ����group����delta
				int curG = set2G[idx];
				bool BexistX = X1.find(bestSet) != X1.end();

				// ����group����delta
				int sizeG = visG[curG].size();
				if (sizeG == 2 && BexistX) {
					for (auto s = visG[curG].begin(); s != visG[curG].end(); ++s) {
						if (*s != bestSet) delta[new_psc.SMap[*s]] += new_psc.GCost;
					}
				}
				else if (sizeG == 1) {
					if (!BexistX) {
						auto s = visG[curG].begin();
						delta[new_psc.SMap[*s]] -= new_psc.GCost;
					}
					else {
						for (auto s = new_psc.group[curG].begin(); s != new_psc.group[curG].end(); ++s)
							if(*s != bestSet) delta[new_psc.SMap[*s]] -= new_psc.GCost;
					}
				}
				else if (sizeG == 0) {
					for (auto s = new_psc.group[curG].begin(); s != new_psc.group[curG].end(); ++s)
						if(*s != bestSet) delta[new_psc.SMap[*s]] += new_psc.GCost;
				}

				// ����element����delta
				for (auto e = new_psc.coveringSet[idx].begin(); e != new_psc.coveringSet[idx].end(); ++e) {
					int sizeE = visE[*e].size();
					if (sizeE == 2 && BexistX) {
						for (auto s = visE[*e].begin(); s != visE[*e].end(); ++s)
							if (*s != bestSet) delta[new_psc.SMap[*s]] -= new_psc.profit[*e];
					}
					else if (sizeE == 1) {
						if (BexistX) {
							for (auto s = e2Set[*e].begin(); s != e2Set[*e].end(); ++s) {
								if (*s == bestSet) continue;
								delta[new_psc.SMap[*s]] += new_psc.profit[*e];
							}
						}
						else {
							auto s = visE[*e].begin();
							delta[new_psc.SMap[*s]] += new_psc.profit[*e];
						}
					}
					else if (sizeE == 0) {
						for (auto s = e2Set[*e].begin(); s != e2Set[*e].end(); ++s)
							if (*s != bestSet) delta[new_psc.SMap[*s]] -= new_psc.profit[*e];
					}
				}

				//����X1
				if (X1.find(bestSet) != X1.end()) { //�ڵ�ǰ���У��Ƴ�ȥ
					X1.erase(bestSet);
					visG[curG].erase(bestSet);
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						visE[*eid].erase(bestSet);
					}
				}
				else { //���ڵ�ǰ���У��ƽ���
					X1.insert(bestSet);
					visG[curG].insert(bestSet);
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						visE[*eid].insert(bestSet);
					}
				}
			};

			auto FlipTabuSearch = [&](Sets& X1, double& f_X1) {
				// ���ɱ�����/delta�ļ���
				vector<int> tabuList(new_psc.setNum, 0);
				int iterCnt = 0, non_improve = 0; //��¼�����ִκ�δ�Ľ�����
				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisg = visG;
				while (non_improve < beta && restMilliSec() > 0) {
					iterCnt += 1;
					SetId bestSet;
					unordered_set<SetId> bestSet1, bestSet2;
					double maxProfit1 = -1e8, maxProfit2 = -1e8, maxProfit;
					// ����ȷ�����ɱ������׼�������
					//����ѡ�����
					// 1���ǽ��ɶ���������ֵ��
					// 2�����ɶ�������õ��ܹ��Ľ���ʷ�����ֵ
					// ѡ��1��2�и��õ��Ǹ�
					for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
						SetId sid = (*setN).first;
						int idx = (*setN).second;
						/*if (tabuList[idx] < iterCnt && delta[idx] > maxProfit) {
							maxProfit = delta[idx];
							bestSet = sid;
						}
						else if (tabuList[idx] >= iterCnt && fb < f_X1 + delta[idx] && delta[idx] > maxProfit) {
							maxProfit = delta[idx];
							bestSet = sid;
						}*/

						if (tabuList[idx] < iterCnt) { //�ǽ��ɲ���
							if (delta[idx] > maxProfit1) {
								bestSet1.clear();
								maxProfit1 = delta[idx];
								bestSet1.insert(sid);
							}
							else if (abs(delta[idx] - maxProfit1) < 0.0001) bestSet1.insert(sid);
						}
						else { //���ɲ���
							if (fb < f_X1 + delta[idx] && delta[idx] > maxProfit2) {
								bestSet2.clear();
								maxProfit2 = delta[idx];
								bestSet2.insert(sid);
							}
							else if (abs(delta[idx] - maxProfit2) < 0.0001) bestSet2.insert(sid);
						}
					}
					
					if (maxProfit1 > maxProfit2) {
						maxProfit = maxProfit1;
						bestSet = *next(bestSet1.begin(), fastRand(bestSet1.size()));
					} 
					else {
						maxProfit = maxProfit2;
						bestSet = *next(bestSet2.begin(), fastRand(bestSet2.size()));
					} 

					if (maxProfit == -1e8) continue;
					f_X1 = f_X1 + maxProfit;

					// ������, ����X1��TabuList
					auto start2 = std::chrono::high_resolution_clock::now();
					flip(X1, bestSet);

					auto end2 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
					times2 += elapsed2.count();

					if (X1.find(bestSet) != X1.end())
						tabuList[bestSet] = iterCnt + fastRand(1, 6); 
					else tabuList[bestSet] = iterCnt + new_psc.SMap.size(); //�������ֵƫ���ˣ�
					
					if (fabs(fb - f_X1) < 0.0001 || fb > f_X1) {
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

			//ʹ�æ�'��ʹ���ܵõ�����
			auto SwapDescentSearch = [&](Sets& X1, double& f_X1) {
				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisg = visG;
				Sets Nx1, tmpX = X1;
				vector<double> delta1 = delta;

				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN).first;
					if (X1.find(sid) != X1.end()) continue;
					Nx1.insert(sid);
				}

				// �����'
				int non_improve = 0;
				int iter_cnt = 0;
				while (non_improve == 0 && restMilliSec() > 0) {
					iter_cnt += 1;
					non_improve = 1;
					SetId bestS1, bestS2;
					vector<pair<SetId, SetId>> bestSs;
					double bestdp = -1e8;
					double dsum1 = 0, dsum = 0;
					if (tmpX.size() == 0) continue;

					//ѡ�����������
					for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
						delta1 = delta;
						int curG = set2G[*s1];
						//������
						if (visG[curG].size() == 1 && (*visG[curG].begin() == *s1)) {
							for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
								if(*s2 != *s1)
									delta1[*s2] -= new_psc.GCost;
							}
						}
						//����Ԫ������
						for (auto e = new_psc.coveringSet[*s1].begin(); e != new_psc.coveringSet[*s1].end(); ++e) {
							auto sets = e2Set[*e];
							if (visE[*e].size() == 1 && (*visE[*e].begin() == *s1)) {
								for (auto s2 = sets.begin(); s2 != sets.end(); ++s2)
									if(*s2 != *s1)
										delta1[*s2] += new_psc.profit[*e];
							}
						}

						// flip(s1, X1, Nx1) ->delta
						for (auto tmps = Nx1.begin(); tmps != Nx1.end(); ++tmps) {
							dsum = delta[*s1] + delta1[*tmps];
							if (dsum > bestdp) {
								/*bestS1 = *s1;
								bestS2 = *tmps;
								bestdp = dsum;*/
								bestSs.clear();
								bestSs.push_back(pair<SetId, SetId>(*s1, *tmps));
								bestdp = dsum;
							}
							else if (abs(dsum - bestdp) < 0.0001) bestSs.push_back(pair<SetId, SetId>(*s1, *tmps));
						}
					}
					int sidx = fastRand(bestSs.size());
					bestS1 = bestSs[sidx].first;
					bestS2 = bestSs[sidx].second;
					//tmpX.erase(bestS1);
					Nx1.erase(bestS2);
					//Nx1.insert(bestS1);

					// ���϶���ִ�����ȷ�� s1��s2Ϊ�����������ִ����Щ�������޸���Ӧ��ֵ����
					//f_X1 += delta[bestS1];
					auto start2 = std::chrono::high_resolution_clock::now();
					flip(X1, bestS1);
					//f_X1 += delta[bestS2];
					flip(X1, bestS2);
					auto end2 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
					times2 += elapsed2.count();
					
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
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisG = visG;
				int iter_cnt = 0;
				//if(restMilliSec() > 0){
				while (non_improve == 0 && restMilliSec() > 0) {
					iter_cnt += 1;
					non_improve = 1;
					auto start2 = std::chrono::high_resolution_clock::now();
					FlipTabuSearch(X1, f_X1);
					auto end2 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
					times3 += elapsed2.count();
					/*cerr << "after exe Tabu" << endl;
					bool testDel1 = testDelta(X1, new_psc, delta);*/

					start2 = std::chrono::high_resolution_clock::now();
					SwapDescentSearch(X1, f_X1);
					end2 = std::chrono::high_resolution_clock::now();
					elapsed2 = end2 - start2;
					times4 += elapsed2.count();
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

				/*cerr << "TwoPhaseLS ִ�д���: " << iter_cnt << endl;
				auto end1 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed = end1 - start1;
				std::cout << "Elapsed time: " << elapsed.count() / 1000.0 << " s" << std::endl;*/
			};

			auto Perturbation = [&](Sets& tmpX, int& t_type, double& f_tmpX) {
				if (fastRand(10000) / 10000.0 < gamma[0]) {
					// ִ��Set_Pertubation
					t_type = 0;
					Sets tmpX2 = tmpX;
					unordered_set<SetId> Ns;
					for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
						SetId sid = (*setN).first;
						if (tmpX.find(sid) == tmpX.end()) Ns.insert(sid);
					}

					
					for (auto s = tmpX2.begin(); s != tmpX2.end(); ++s) {
						int len = Ns.size();
						int j = new_psc.SMap[*s];
						if (len == 0) break;
						double isDel = fastRand(10000) / 10000.0;
						if (isDel < 0.3) {
							f_tmpX += delta[j];
							flip(tmpX, *s);
							int idx = fastRand(len);
							auto sid = next(Ns.begin(), idx);
							int sidx = new_psc.SMap[*sid];
							f_tmpX += delta[sidx];
							flip(tmpX, *sid);
							Ns.erase(*sid);
						}
					}
				}
				else {
					// ִ��Group_Pertubation
					t_type = 1;
					Sets tmpX2 = tmpX;
					unordered_set<int> Z, Nz; //Z��ʾ ���еĸ��Ǽ���X�Ľ�����Ϊ�յ������
					double p = 0.3;
					for (int g = 0; g < new_psc.groupNum; g++) {
						if (visG[g].size() >= 1) Z.insert(g);
						else Nz.insert(g);
					}
					int Zlen = Z.size();
					int tochs = max(int(p * Zlen), 1);
					for (int i = 0; i < tochs; ++i) {
						int len = Z.size();
						if (len == 0) break;
						int idx = fastRand(len);
						auto cg = next(Z.begin(), idx); // cgΪѡ������
						int icg = *cg;
						Z.erase(*cg);
						for (auto s = new_psc.group[icg].begin(); s != new_psc.group[icg].end(); ++s) {
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
							//cerr << "�Ŷ����ֵ�����! " << endl;
							break;
						}
						int idx = fastRand(len);
						auto cg = next(Nz.begin(), idx);
						int icg = *cg;
						Nz.erase(*cg);

						int fcnt = tmpX2.size() / Zlen;
						auto tmpg = new_psc.group[icg];
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
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisG = visG;
				while (non_improve < omega && restMilliSec() > 0) {
					iter_cnt += 1;
					auto start2 = std::chrono::high_resolution_clock::now();
					TwoPhaseLS(Xp, fp);
					auto end2 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
					times += elapsed2.count();
					//cerr << elapsed2.count() / 1000.0 << endl;

					if (abs(fp - tmp_f) <= 0.0001 || fp < tmp_f) non_improve += 1;
					else {
						// ���¦� 
						if (t_type == 0) d1 += 1;
						else if (t_type == 1) d2 += 1;
						gamma[0] = (d0 + d1) / (2 * d0 + d1 + d2); 
						gamma[1] = 1 - gamma[0];
						cerr << "gamma0: " << gamma[0] << endl;

						// ����eta
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
							// ����ƽ������
							if (eta[j] > alpha) eta[j] = (1 - phi3) * eta[j];
							else if (eta[j] < 1 - alpha) eta[j] = phi3 + (1 - phi3) * eta[j];
						
						}

						tmpX = Xp;
						tmp_f = fp;
						tmpDel = delta;
						tmpvise = visE;
						tmpvisG = visG;
						non_improve = 0; 
						cerr << "��ǰ��ý��Ϊ: " << tmp_f << endl;
						cerr << "d1: " << d1 << "; d2: " << d2 << endl;
					}
					
					Xp = tmpX;
					fp = tmp_f;
					visE = tmpvise;
					visG = tmpvisG;
					delta = tmpDel;
					Perturbation(Xp, t_type, fp);
				}
				cerr << "IntensifivationDrivenILS ִ�д���: " << iter_cnt << endl;
				f_X0 = tmp_f;

				cerr << "TwoPhaseLS��ִ��ʱ�䣺" << times / 1000.0 << " s" << endl;
				cerr << "flip����ִ��ʱ��: " << times2 / 1000.0 << " s" << endl;
				cerr << "Tabu Searchʱ��Ϊ: " << times3 / 1000.0 << " s" << endl;
				cerr << "Swap Searchʱ��Ϊ: " << times4 / 1000.0 << " s" << endl;
				times = 0;
				times2 = 0;
				times3 = 0;
				times4 = 0;

				auto end = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed = end - start;
				std::cout << "Elapsed time: " << elapsed.count() / 1000.0 << " s" << std::endl;
				return tmpX;
			};

			while (restMilliSec() > 0) {
				// ��ó�ʼ���Ҫȷ���������ͳ�ʼ�������ֵ����f_X0
				double f_X0 = 0;
				X0 = LearningDrivenInitialization();
				// ��������ֵ
				f_X0 = calProfit(X0, new_psc);
				// ����ĺ��� ��visG��visE
				fill(delta.begin(), delta.end(), 0);
				for (ElemId eid = 0; eid < new_psc.elemNum; ++eid)
					visE[eid].clear();
				for (int gid = 0; gid < new_psc.groupNum; ++gid)
					visG[gid].clear();

				for (auto s = X0.begin(); s != X0.end(); ++s) {
					visG[set2G[*s]].insert(*s);
					for (auto eid = new_psc.coveringSet[*s].begin(); eid != new_psc.coveringSet[*s].end(); ++eid)
						visE[*eid].insert(*s);
				}

				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN).first;
					int idx = (*setN).second;
					// ��ǰ���Ǽ�λ�ڳ�ʼ����
					if (X0.find(sid) != X0.end()) {
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
							if (visE[*eid].size() == 1) delta[idx] -= new_psc.profit[*eid];
						}
						delta[idx] += new_psc.SCost[idx];
						if (visG[set2G[idx]].size() == 1) delta[idx] += new_psc.GCost;
					}
					else { //��ǰ���Ǽ����ڳ�ʼ����
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
							if (visE[*eid].size() == 0) delta[idx] += new_psc.profit[*eid];
						}
						delta[idx] -= new_psc.SCost[idx];
						if (visG[set2G[idx]].size() == 0) delta[idx] -= new_psc.GCost;
					}
				}
				
				cerr << "IFDִ��ǰ������ֵΪ��" << f_X0 << endl;
				X0 = IntensifivationDrivenILS(X0, f_X0);
				double testf = calProfit(X0, new_psc);
				if (testf - f_X0 >= 0.00001 || testf - f_X0 <= -0.00001) {
					cerr << "�������������⣡" << endl;
					cerr << "realf :" << testf << " f_X0: " << f_X0 << endl;
				}
				
				// ȷ����ǰ����֮ǰ�õ��Ľ�����ƶ�
				int sameCnt = 0;
				for (auto s = X0.begin(); s != X0.end(); ++s) {
					if (best_X.find(*s) != best_X.end()) sameCnt += 1;
				}
				cerr << "�ֲ����Ž�����ƶ�Ϊ��" << sameCnt / (double)best_X.size() << endl;
				
				if (f_X0 > best_f) {
					best_X = X0;
					best_f = f_X0;
				} 
				cerr << "��ǰ��Ĵ�СΪ��" << best_X.size() << endl;
				cerr << "��ǰ�������ֵΪ��" << best_f << endl << endl;
			}
			double real_f = calProfit(best_X, new_psc);
			cerr << "��ʵ�������ֵΪ��" << real_f << endl;
			cerr << "�������������ֵΪ: " << best_f << endl;
			return best_f;
		}
	};

	double solvePMForSetCovering(Sets& output, PSetCovering& input, std::function<long long()> restMilliSec, int seed) {
		return Solver().solve(output, input, restMilliSec, seed);
	}
}

