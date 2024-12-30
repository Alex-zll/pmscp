#include "pmscp.h"

#include <random>
#include <iostream>
#include <time.h>
#include <algorithm>
#include <chrono>
#include <fstream>

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
		double calProfit(Sets X, PSetCovering psc, vector<int> set2G, vector<unordered_set<SetId>>& visE, vector<unordered_set<SetId>>& visG) {
			double res = 0;
			for (auto tmpS = X.begin(); tmpS != X.end(); ++tmpS) {
				int idx = *tmpS;
				int gid = set2G[*tmpS];
				res -= psc.SCost[idx];
				if (visG[gid].size() == 0) {
					res -= psc.GCost;
					visG[gid].insert(*tmpS);
				}

				for (auto Eid = psc.coveringSet[idx].begin(); Eid != psc.coveringSet[idx].end(); ++Eid) {
					if (visE[*Eid].size() == 0) {
						res += psc.profit[*Eid];
						visE[*Eid].insert(*tmpS);
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
					set2G[*tmps] = gid;
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
				SetId sid = (*setN);
				int idx = (*setN);
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
				SetId sid = (*setN);
				int idx = (*setN);
				if (delta[idx] - testDel[idx] <= 0.00001 && delta[idx] - testDel[idx] >= -0.00001) continue;
				else {
					cerr << "当前delta的增量计算有问题!" << endl;
					return false;
				}
			}
			return true;
		}
		void judgeVis(vector<unordered_set<SetId>> visE, vector<unordered_set<SetId>> visG, Sets X, PSetCovering psc) {
			vector<unordered_set<SetId>> tmpE(psc.elemNum), tmpG(psc.groupNum);
			vector<int> set2G(psc.setNum);
			int flag = 0;
			for (int gid = 0; gid < psc.groupNum; ++gid) {
				for (auto tmps = psc.group[gid].begin(); tmps != psc.group[gid].end(); ++tmps) {
					set2G[*tmps] = gid;
				}
			}
			for (auto s = X.begin(); s != X.end(); ++s) {
				int curG = set2G[*s];
				if (visG[curG].find(*s) == visG[curG].end()) {
					flag = 1;
					cerr << "visG 计算有问题! " << endl;
				}
				tmpG[curG].insert(*s);

				for (auto e = psc.coveringSet[*s].begin(); e != psc.coveringSet[*s].end(); ++e) {
					if (visE[*e].find(*s) == visE[*e].end()) {
						flag = 1;
						cerr << "visE 计算有问题！" << endl;
					}
					tmpE[*e].insert(*s);
				}
			}

			for (int idx = 0; idx < tmpG.size(); ++idx) {
				if (tmpG[idx].size() != visG[idx].size()) {
					flag = 1;
					cerr << "visG 计算有问题" << endl;
				} 
			}

			for (int idx = 0; idx < tmpE.size(); ++idx) {
				if (tmpE[idx].size() != visE[idx].size()) {
					flag = 1;
					cerr << "visE 计算有问题" << endl;
				} 
			}
			
			if (flag == 0) cerr << "vis 没有问题" << endl;
			else cerr << "vis 有问题" << endl;
		}
		PSetCovering Reduction(PSetCovering psc) {
			//进行规约操作后，setNum、coveringSet、gourp、SCost都可能相应发生改变
			int new_setNum = psc.setNum;

			// 首先确定要被删除的覆盖集
			vector<int> delSetList(psc.setNum, 0);
			for (int sid = 0; sid < psc.setNum; ++sid) {
				double pft = 0;
				for (auto eid = psc.coveringSet[sid].begin(); eid != psc.coveringSet[sid].end(); ++eid) {
					pft += psc.profit[*eid];
				}
				if (pft <= psc.SCost[sid]) delSetList[sid] = 1;
			}

			// 依次删除这些覆盖集
			for (auto s = 0; s < psc.setNum; ++s) {
				if (delSetList[s] == 1) {
					new_setNum -= 1;
					for (int gid = 0; gid < psc.groupNum; ++gid) {
						if (psc.group[gid].find(s) != psc.group[gid].end()) {
							psc.group[gid].erase(s);
						}
					}
				}
				else psc.SMap.push_back(s);
				
			}
			return psc;
		}
		void CoveringRate(PSetCovering psc, string testFile) {
			PSetCovering new_psc = Reduction(psc);
			vector<int> ratio(8, 0);
			vector<string> rate = {"<0.1%", "0.1%~0.5%", "0.5%~1%","1%~3%", "3%~5%", "5%~10%" ,"10%~30%", ">30%"};
			int eleCnt = psc.elemNum;
			for (auto s = psc.SMap.begin(); s != psc.SMap.end(); ++s) {
				int idx = (*s);
				double num = psc.coveringSet[idx].size();
				double rto = num / eleCnt;
				if (rto < 0.001) ratio[0] += 1;
				else if (rto < 0.005 && rto >= 0.001) ratio[1] += 1;
				else if (rto >= 0.005 && rto < 0.01) ratio[2] += 1;
				else if (rto >= 0.01 && rto < 0.03) ratio[3] += 1;
				else if (rto >= 0.03 && rto < 0.05) ratio[4] += 1;
				else if (rto >= 0.05 && rto < 0.1) ratio[5] += 1;
				else if (rto >= 0.1 && rto < 0.3) ratio[6] += 1;
				else ratio[7] += 1;
			}
			for (int i = 0; i < 8; ++i) {
				cerr << rate[i] << ": " << ratio[i] << endl;
			}

			ofstream outfile;
			string fileName = "D:/0HustWork/hust-exercise/PMSCP/ratio.csv";
			outfile.open(fileName, std::ios::app); // 使用 ios::app 进行追加
			if (!outfile.is_open()) {
				std::cerr << "无法打开文件：" << fileName << std::endl;
				return;
			}
			outfile << endl;
			for (int i = 0; i < 8; ++i) {
				outfile << testFile << "," << rate[i] << "," << ratio[i] << endl;
			}
			//outfile << rate[0] << "," << ratio[0] << endl;

			// 关闭文件流
			outfile.close();

			std::cout << "数据追加写入完成" << std::endl;
		}
		void CoveredRate(PSetCovering psc, string testFile) {
			cout << "执行 CoveredRate" << endl;
			PSetCovering new_psc = Reduction(psc);
			vector<int> ratio(10, 0);
			vector<string> rate = { "<200", "200~400", "400~600","600~800", "800~1000", "1000~1200", "1200~1400", "1400~1600"
								   , "1600~1800", ">1800"};
			vector<unordered_set<SetId>> e2Set(new_psc.elemNum); //确定element由哪些覆盖集所覆盖
			for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
				SetId sid = (*setN);
				int idx = (*setN);
				for (auto e = new_psc.coveringSet[idx].begin(); e != new_psc.coveringSet[idx].end(); ++e)
					e2Set[*e].insert(sid);
			}
			for (int i = 0; i < new_psc.elemNum; ++i) {
				int coveredNum = e2Set[i].size();
				if (coveredNum < 200) ratio[0] += 1;
				else if (coveredNum >= 200 && coveredNum < 400) ratio[1] += 1;
				else if (coveredNum >= 400 && coveredNum < 600) ratio[2] += 1;
				else if (coveredNum >= 600 && coveredNum < 800) ratio[3] += 1;
				else if (coveredNum >= 800 && coveredNum < 1000) ratio[4] += 1;
				else if (coveredNum >= 1000 && coveredNum < 1200) ratio[5] += 1;
				else if (coveredNum >= 1200 && coveredNum < 1400) ratio[6] += 1;
				else if (coveredNum >= 1400 && coveredNum < 1600) ratio[7] += 1;
				else if (coveredNum >= 1600 && coveredNum < 1800) ratio[8] += 1;
				else ratio[9] += 1;
			}

			ofstream outfile;
			string fileName = "D:/0HustWork/hust-exercise/PMSCP/coveredRatio.csv";
			outfile.open(fileName, std::ios::app); // 使用 ios::app 进行追加
			if (!outfile.is_open()) {
				std::cerr << "无法打开文件：" << fileName << std::endl;
				return;
			}
			outfile << endl;
			for (int i = 0; i < 10; ++i) {
				outfile << testFile << "," << rate[i] << "," << ratio[i] << endl;
			}
			//outfile << rate[0] << "," << ratio[0] << endl;

			// 关闭文件流
			outfile.close();

			cout << "数据追加写入完成" << endl;
		}

		void element2Group(PSetCovering psc) {
			vector<vector<int>> groupElem(psc.groupNum);
			vector<int> groupElemNum(psc.groupNum);
			vector<int> sameElemCnt(psc.groupNum, 0);
			for (int i = 0; i < psc.groupNum; ++i) groupElem[i].resize(psc.elemNum, 0);
			
			for (int i = 0; i < psc.groupNum; ++i) {
				for (auto s = psc.group[i].begin(); s != psc.group[i].end(); ++s) {
					for (auto e = psc.coveringSet[*s].begin(); e != psc.coveringSet[*s].end(); ++e)
						groupElem[i][*e] = 1;
				}
				for(int en = 0; en < psc.elemNum; ++en)
					if (groupElem[i][en] == 1) groupElemNum[i] += 1;
			}


			for (int i = 0; i < psc.groupNum - 1; ++i) {
				for (int en = 0; en < psc.elemNum; ++en) {
					if (groupElem[i][en] == groupElem[i + 1][en] && groupElem[i][en] == 1) sameElemCnt[i] += 1;
				}
			}
			cerr << "相邻组计算完毕" << endl;
		}

		PSetCovering calDomainSet(PSetCovering psc) {
			vector<int> delSetList(psc.setNum, 0);
			vector<unordered_set<SetId>> covering_set(psc.setNum);
			vector<int> SMap_pos(psc.setNum, -1);
			auto start1 = std::chrono::high_resolution_clock::now();
			int idx1 = 0;
			for (auto sets = psc.coveringSet.begin(); sets != psc.coveringSet.end(); ++sets) {
				for (auto s = (*sets).begin(); s != (*sets).end(); ++s)
					covering_set[idx1].insert(*s);
				idx1 += 1;
			}

			for (int idx = 0; idx < psc.SMap.size(); ++idx)
				SMap_pos[psc.SMap[idx]] = idx;

			for (int sid1 = 0; sid1 < psc.setNum; ++sid1) {
				if (delSetList[sid1] == 1) continue;

				for (int sid2 = sid1 + 1; sid2 < psc.setNum; ++sid2) {
					if (delSetList[sid1] == 1) break;
					/*if (cnt1 == 102)
						cerr << "这里开始" << endl;*/
					if (delSetList[sid2] == 1) continue;
					if (sid1 == sid2)
						continue;

					if (psc.SCost[sid1] < psc.SCost[sid2] && psc.coveringSet[sid2].size() <= psc.coveringSet[sid1].size()) {
						int cnt = 0;
						for (auto e = psc.coveringSet[sid2].begin(); e != psc.coveringSet[sid2].end(); ++e) {
							//if (psc.coveringSet[sid1].find(*e) == psc.coveringSet[sid1].end()) break;
							/*if (find(psc.coveringSet[sid1].begin(), psc.coveringSet[sid1].end(), *e) == psc.coveringSet[sid1].end()) break;*/
							if (covering_set[sid1].find(*e) == covering_set[sid1].end()) break;
							cnt += 1;
						}
						if (cnt == psc.coveringSet[sid2].size()) {
							delSetList[sid2] = 1;
							//psc.SMap.erase(sid2);
						}
					}
					else if (psc.SCost[sid2] < psc.SCost[sid1] && psc.coveringSet[sid1].size() <= psc.coveringSet[sid2].size()) {
						int cnt = 0;
						for (auto e = psc.coveringSet[sid1].begin(); e != psc.coveringSet[sid1].end(); ++e) {
							//if (psc.coveringSet[sid2].find(*e) == psc.coveringSet[sid2].end()) break;
							//if (find(psc.coveringSet[sid2].begin(), psc.coveringSet[sid2].end(), *e) == psc.coveringSet[sid2].end()) break;
							if (covering_set[sid2].find(*e) == covering_set[sid2].end()) break;
							cnt += 1;
						}
						if (cnt == psc.coveringSet[sid1].size()) {
							delSetList[sid1] = 1;
							//psc.SMap.erase(sid1);
						}
					}
				}
			}
			auto end1 = std::chrono::high_resolution_clock::now();
			std::chrono::duration<double, std::milli> elapsed1 = end1 - start1;

			double times1 = elapsed1.count();
			cerr << "time of calculate domain set: " << times1 / 1000.0 << " s" << endl;
			// 依次删除这些覆盖集
			for (SetId s = 0; s < psc.setNum; ++s) {
				if (delSetList[s] == 1) {
					for (int gid = 0; gid < psc.groupNum; ++gid) {
						if (psc.group[gid].find(s) != psc.group[gid].end()) {
							psc.group[gid].erase(s);
						}
					}
					
					if (SMap_pos[s] != -1) {
						int len = psc.SMap.size();
						psc.SMap[SMap_pos[s]] = psc.SMap[len - 1];
						SMap_pos[psc.SMap[len - 1]] = SMap_pos[s];
						SMap_pos[s] = -1;
						psc.SMap.pop_back();
					}
				}
					
			}
			return psc;
		}

		PSetCovering calDomainSet1(PSetCovering psc) {
			vector<int> delSetList(psc.setNum);
			unordered_set<SetId> delSets;
			vector<unordered_set<SetId>> covering_set(psc.setNum);
			vector<int> SMap_pos(psc.setNum, -1);
			auto start1 = std::chrono::high_resolution_clock::now();

			int idx = 0;
			for (auto sets = psc.coveringSet.begin(); sets != psc.coveringSet.end(); ++sets) {
				for (auto s = (*sets).begin(); s != (*sets).end(); ++s)
					covering_set[idx].insert(*s);
				idx += 1;
			}

			for (int idx = 0; idx < psc.SMap.size(); ++idx)
				SMap_pos[psc.SMap[idx]] = idx;

			for (int sid1 = 0; sid1 < psc.setNum; ++sid1) {
				if (delSetList[sid1] == 1) continue;

				for (int sid2 = sid1 + 1; sid2 < psc.setNum; ++sid2) {
					if (delSetList[sid1] == 1) break;
					/*if (cnt1 == 102)
						cerr << "这里开始" << endl;*/
					if (delSetList[sid2] == 1) continue;
					if (sid1 == sid2)
						continue;

					if (psc.SCost[sid1] <= psc.SCost[sid2] && psc.coveringSet[sid2].size() <= psc.coveringSet[sid1].size()) {
						int cnt = 0;
						for (auto e = psc.coveringSet[sid2].begin(); e != psc.coveringSet[sid2].end(); ++e) {
							//if (psc.coveringSet[sid1].find(*e) == psc.coveringSet[sid1].end()) break;
							//if (find(psc.coveringSet[sid1].begin(), psc.coveringSet[sid1].end(), *e) == psc.coveringSet[sid1].end()) break;
							if (covering_set[sid1].find(*e) == covering_set[sid1].end()) break;
							cnt += 1;
						}
						if (cnt == psc.coveringSet[sid2].size()) {
							delSetList[sid2] = 1;
						}
					}
					else if (psc.SCost[sid2] <= psc.SCost[sid1] && psc.coveringSet[sid1].size() <= psc.coveringSet[sid2].size()) {
						int cnt = 0;
						for (auto e = psc.coveringSet[sid1].begin(); e != psc.coveringSet[sid1].end(); ++e) {
							//if (psc.coveringSet[sid2].find(*e) == psc.coveringSet[sid2].end()) break;
							//if (find(psc.coveringSet[sid2].begin(), psc.coveringSet[sid2].end(), *e) == psc.coveringSet[sid2].end()) break;
							if (covering_set[sid2].find(*e) == covering_set[sid2].end()) break;
							cnt += 1;
						}
						if (cnt == psc.coveringSet[sid1].size()) 
							delSetList[sid1] = 1;
					}
				}
			}
			auto end1 = std::chrono::high_resolution_clock::now();
			std::chrono::duration<double, std::milli> elapsed1 = end1 - start1;

			double times1 = elapsed1.count();
			cerr << "time of calculate domain set: " << times1 / 1000.0 << " s" << endl;
			// 依次删除这些覆盖集
			for (SetId s = 0; s < psc.setNum; ++s) {
				if (delSetList[s] == 1) {
					for (int gid = 0; gid < psc.groupNum; ++gid) {
						if (psc.group[gid].find(s) != psc.group[gid].end()) {
							psc.group[gid].erase(s);
						}
					}

					if (SMap_pos[s] != -1) {
						int len = psc.SMap.size();
						psc.SMap[SMap_pos[s]] = psc.SMap[len - 1];
						SMap_pos[psc.SMap[len - 1]] = SMap_pos[s];
						SMap_pos[s] = -1;
						psc.SMap.pop_back();
					}
				}
			}
			return psc;
		}

		PSetCovering calDomainSet2(PSetCovering psc) {
			vector<int> delSetList(psc.setNum);
			unordered_set<SetId> delSets;
			vector<unordered_set<SetId>> covering_set(psc.setNum);
			auto start1 = std::chrono::high_resolution_clock::now();
		};

		//PSetCovering calDomainSet2(PSetCovering psc) {
		//	vector<int> delSetList(psc.setNum);
		//	vector<double> pureProfit(psc.setNum, 0);
		//	unordered_set<SetId> delSets;
		//	CSet tmpMap = psc.SMap;
		//	auto start1 = std::chrono::high_resolution_clock::now();
		//	for (int sid = 0; sid < psc.setNum; ++sid) {
		//		for (auto e = psc.coveringSet[sid].begin(); e != psc.coveringSet[sid].end(); ++e) {
		//			pureProfit[sid] += psc.profit[*e];
		//		}
		//	}
		//	for (int i = 0; i < psc.groupNum; ++i) {
		//		vector<int> tmpG;
		//		for (auto s = psc.group[i].begin(); s != psc.group[i].end(); ++s) {
		//			tmpG.push_back(psc.SMap[*s]);
		//		}
		//		for (int i = 0; i < tmpG.size(); ++i) {
		//			int sid1 = tmpG[i];
		//			if (delSetList[sid1] == 1) continue;
		//			for (int j = i + 1; j < tmpG.size(); ++j) {
		//				int sid2 = tmpG[j];
		//				if (delSetList[sid1] == 1) break;
		//				if (delSetList[sid2] == 1) continue;
		//				if (sid1 == sid2)
		//					continue;
		//				if (psc.coveringSet[sid2].size() <= psc.coveringSet[sid1].size()) {
		//					int cnt = 0;
		//					for (auto e = psc.coveringSet[sid2].begin(); e != psc.coveringSet[sid2].end(); ++e) {
		//						if (psc.coveringSet[sid1].find(*e) == psc.coveringSet[sid1].end()) break;
		//						cnt += 1;
		//					}
		//					if (cnt == psc.coveringSet[sid2].size()) {
		//						if (pureProfit[sid1] - pureProfit[sid2] - psc.SCost[sid1] < 0) {
		//							delSetList[sid1] = 1;
		//							psc.SMap.erase(sid1);
		//							delSets.insert(sid1);
		//						}
		//						else {
		//							delSetList[sid2] = 1;
		//							psc.SMap.erase(sid2);
		//							delSets.insert(sid2);
		//						}
		//					}
		//				}
		//				else {
		//					int cnt = 0;
		//					for (auto e = psc.coveringSet[sid1].begin(); e != psc.coveringSet[sid1].end(); ++e) {
		//						if (psc.coveringSet[sid2].find(*e) == psc.coveringSet[sid2].end()) break;
		//						cnt += 1;
		//					}
		//					if (cnt == psc.coveringSet[sid1].size()) {
		//						if (pureProfit[sid2] - pureProfit[sid1] - psc.SCost[sid2] < 0) {
		//							delSetList[sid2] = 1;
		//							psc.SMap.erase(sid2);
		//							delSets.insert(sid2);
		//						}
		//						else {
		//							delSetList[sid1] = 1;
		//							psc.SMap.erase(sid1);
		//							delSets.insert(sid1);
		//						}
		//					}
		//				}
		//			}
		//		}
		//	}
		//	auto end1 = std::chrono::high_resolution_clock::now();
		//	std::chrono::duration<double, std::milli> elapsed1 = end1 - start1;
		//
		//	double times1 = elapsed1.count();
		//	cerr << "time of calculate domain set: " << times1 / 1000.0 << " s" << endl;
		//	// 依次删除这些覆盖集
		//	for (auto s = delSets.begin(); s != delSets.end(); ++s) {
		//		SetId dset = *s;
		//
		//		for (int gid = 0; gid < psc.groupNum; ++gid) {
		//			if (psc.group[gid].find(dset) != psc.group[gid].end()) {
		//				psc.group[gid].erase(dset);
		//			}
		//		}
		//	}
		//	return psc;
		//}

		void checkDel(PSetCovering psc) {
			SetId sid;
			cin >> sid;
			while (sid != -1) {
				if (find(psc.SMap.begin(), psc.SMap.end(), sid) != psc.SMap.end()) {
					cout << "error! " << sid << " is deleted! " << endl;
				}
				cin >> sid;
			}
		}

		double solve(Sets& X, PSetCovering& psc, function<long long()> restMilliSec, int seed) {
			initRand(seed);
			double epsilon = 0.6; //ε表示贪心选择的概率
			int omega = 250, beta = 1000; //ω表示局部搜索的迭代轮次；β表示禁忌搜索的深度
			PSetCovering new_psc;
			double times1 = 0;
			auto start1 = std::chrono::high_resolution_clock::now();
			// 首先对覆盖集进行化简
			new_psc = Reduction(psc);
			if (psc.setNum < 500000) {
				if (psc.setNum >= 10000 && psc.setNum < 30000)
					new_psc = calDomainSet(new_psc);
				else new_psc = calDomainSet1(new_psc);
			}
				
			//new_psc = calDomainSet1(new_psc);
				
			//PSetCovering new_psc = psc; 
			auto end1 = std::chrono::high_resolution_clock::now();
			std::chrono::duration<double, std::milli> elapsed1 = end1 - start1;
			
			times1 += elapsed1.count();
			cerr << "time of reduce and calculate domain set: " << times1 / 1000.0 << " s" << endl;

			//checkDel(new_psc);

			Sets best_X, X0, X1;
			double best_f = 0; //记录最高的收益
			vector<double> eta(new_psc.setNum, 0.5); //η表示初始化的历史信息向量
			vector<double> gamma(2, 0.5); //γ表示扰动概率的向量 
			vector<unordered_set<SetId>> visE(new_psc.elemNum); //确定e被解中的哪几个集合覆盖
			vector<unordered_set<SetId>> visG(new_psc.groupNum); //确定解中有哪些集合属于同一个组
			vector<double> delta(new_psc.setNum, 0); //快速评估邻域解的质量
			vector<int> set2G(new_psc.setNum); //确定覆盖集属于哪个组
			vector<vector<SetId>> e2Set(new_psc.elemNum); //确定element由哪些覆盖集所覆盖
			vector<int> stagGroup(new_psc.groupNum, 0); //明确阻滞哪个group
			double d0 = 50, d1 = 0, d2 = 0; //确定扰动的选择
			int tot_iterCnt = 0; //计算总迭代次数
			int flipIterCnt = 0, swapIterCnt = 0; //单一禁忌搜索迭代次数和交换搜索迭代次数
			int pftIterCnt = 0;

			double times = 0, times2 = 0, times3 = 0, times4 = 0, times5 = 0, times6 = 0, times7 = 0;

			for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
				SetId sid = (*setN); 
				int idx = (*setN);
				for (auto e = new_psc.coveringSet[idx].begin(); e != new_psc.coveringSet[idx].end(); ++e)
					e2Set[*e].push_back(sid);
			}
			
			for (int gid = 0; gid < new_psc.groupNum; ++gid) {
				for (auto tmps = new_psc.group[gid].begin(); tmps != new_psc.group[gid].end(); ++tmps) {
					set2G[*tmps] = gid;
				}
			}

			//精简组的数量 好像没有效果
			
			//auto reduceGroup = [&](Sets& X1) {
			//	vector<unordered_set<SetId>> x_group(new_psc.groupNum);
			//	double negPft = 0;
			//	for (auto s = X1.begin(); s != X1.end(); ++s) 
			//		x_group[set2G[*s]].insert(*s);
			//	for (int g = 0; g < new_psc.groupNum; ++g) {
			//		if (x_group[g].size() == 0) continue;
			//		int flag = 0;
			//		//确定是否每一个子集都有可以替换的子集
			//		for (auto s = x_group[g].begin(); s != x_group[g].end(); ++s) {
			//			if (domSet[*s].size() == 0) {
			//				flag = 1;
			//				break;
			//			}
			//			int tmpf = 0;
			//			for (auto ds = domSet[*s].begin(); ds != domSet[*s].end(); ++ds) {
			//				if (x_group[set2G[*ds]].size() == 0) continue;
			//				tmpf = 1;
			//			}
			//			if (tmpf == 0) flag = 1;
			//				
			//		}
			//		if (flag == 1) continue;
			//
			//		// 选择可以替换的子集
			//		vector<unordered_set<SetId>> tmpvisE = visE;
			//		double sumCost = 0;
			//		vector<SetId> tochg;
			//		for (auto s = x_group[g].begin(); s != x_group[g].end(); ++s) {
			//			// 计算s换出后产生的损失值
			//			double curcost = new_psc.SCost[*s];
			//			for (auto e = new_psc.coveringSet[*s].begin(); e != new_psc.coveringSet[*s].end(); ++e) {
			//				if (tmpvisE[*e].size() == 1) curcost -= new_psc.profit[*e];
			//				tmpvisE[*e].erase(*s);
			//			}
			//			sumCost += curcost;
			//
			//			// 将收益值最大的子集换入
			//			double maxpft = -1e8;
			//			SetId bests;
			//			for(auto ds = domSet[*s].begin(); ds != domSet[*s].end(); ++ds){
			//				if (x_group[set2G[*ds]].size() == 0) continue;
			//				double tmpPft = -new_psc.SCost[*ds];
			//				for (auto e = new_psc.coveringSet[*ds].begin(); e != new_psc.coveringSet[*ds].end(); ++e)
			//					if (tmpvisE[*e].size() == 0) tmpPft += new_psc.profit[*e];
			//				if (maxpft < tmpPft) {
			//					maxpft = tmpPft;
			//					bests = *ds;
			//				}
			//			}
			//			for (auto e = new_psc.coveringSet[bests].begin(); e != new_psc.coveringSet[bests].end(); ++e)
			//				tmpvisE[*e].insert(bests);
			//			tochg.push_back(bests);
			//			sumCost += maxpft;
			//		}
			//		// 可以进行组的精简
			//		if (sumCost + new_psc.GCost > 0) {
			//			visG[g].clear();
			//			for (auto s = x_group[g].begin(); s != x_group[g].end(); ++s)
			//				X1.erase(*s);
			//			for (auto s = tochg.begin(); s != tochg.end(); ++s) {
			//				X1.insert(*s);
			//				for (auto e = new_psc.coveringSet[*s].begin(); e != new_psc.coveringSet[*s].end(); ++e)
			//					visE[*e].insert(*s);
			//			}
			//			x_group[g].clear();
			//		}
			//	}
			//
			//};

			// 纯随机初始化
			auto LearningDrivenInitialization = [&]() { //使用 psc; epsilon; eta三个变量
				Sets tmpX;
				unordered_set<SetId> tmpS;
				vector<int> tmpVisE(new_psc.elemNum, 0), tmpVisG(new_psc.groupNum, 0);
				
				for (auto smp = new_psc.SMap.begin(); smp != new_psc.SMap.end(); ++smp) 
					tmpS.insert(*smp);
				
				while (tmpS.size() > 0) {
					SetId sid;
					double rNum = fastRand(10000) / 10000.0;
					
					auto it = next(tmpS.begin(), fastRand(tmpS.size()));
					sid = *it;
					
					tmpS.erase(sid);

					double gainCnt = 0;
					int idx = sid;
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						if (tmpVisE[*eid] == 0)
							gainCnt += new_psc.profit[*eid];	 
					}
					/*if (tmpVisG[set2G[sid]] == 0) gainCnt -= new_psc.GCost;*/
					rNum = fastRand(10000) / 10000.0;
					if (gainCnt > new_psc.SCost[idx]) {
						tmpX.insert(sid);
						tmpVisG[set2G[sid]] = 1;
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) 
							tmpVisE[*eid] = 1;
					} 
				}
				return tmpX;
			};

			auto LearningDrivenInitialization1 = [&]() {
				Sets tmpX;
				unordered_set<SetId> tmpS;
				vector<double> tmp_delta(new_psc.setNum, 0);
				vector<unordered_set<SetId>> tmp_visE(new_psc.elemNum); //确定e被解中的哪几个集合覆盖
				vector<unordered_set<SetId>> tmp_visG(new_psc.groupNum); //确定解中有哪些集合属于同一个组
				for (auto smp = new_psc.SMap.begin(); smp != new_psc.SMap.end(); ++smp)
					tmpS.insert(*smp);

				while (tmpS.size() > 0) {
					SetId sid;
					double rNum = fastRand(10000) / 10000.0;
					double maxP = 0;
					vector<SetId> sids;
					if (rNum < epsilon) {
						for (auto inflect = tmpS.begin(); inflect != tmpS.end(); ++inflect) {
							SetId sid1 = (*inflect);
							int idx = sid1;
							if (abs(maxP - eta[idx]) < 0.0001) sids.push_back(sid1);
							else if (maxP < eta[idx]) {
								sids.clear();
								maxP = eta[idx];
								//sid = sid1;
								sids.push_back(sid1);
							}	 
						}
						sid = sids[fastRand(sids.size())];
						/*tmpS.erase(sid);
						if (fastRand(10000) / 10000.0 > eta[sid]) continue;*/
					}
					else {
						auto it = next(tmpS.begin(), fastRand(tmpS.size()));
						sid = *it;
					}
					tmpS.erase(sid);
					double gainCnt = 0;
					int idx = sid;
					gainCnt -= new_psc.SCost[idx];
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						if (tmp_visE[*eid].size() == 0)
							gainCnt += new_psc.profit[*eid];
					}
					rNum = fastRand(10000) / 10000.0;
					if (gainCnt > 0 && rNum < eta[sid]) {
						tmpX.insert(sid);
						tmp_visG[set2G[sid]].insert(sid);
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid)
							tmp_visE[*eid].insert(sid);
					}
				}
				return tmpX;
			};
			
			// flip也进行了改动，用于提升性能
			auto flip = [&](SetId bestSet) {
				int idx = bestSet;
				// 调整自己的delta
				delta[idx] = -delta[idx];
				// 根据group调整delta
				int curG = set2G[idx];
				bool BexistX = X1.find(bestSet) != X1.end();

				// 根据group调整delta
				int sizeG = visG[curG].size();
				if (sizeG == 2 && BexistX) {
					for (auto s = visG[curG].begin(); s != visG[curG].end(); ++s) {
						if (*s != bestSet) delta[*s] += new_psc.GCost;
					}
				}
				else if (sizeG == 1) {
					if (!BexistX) {
						auto s = visG[curG].begin();
						delta[*s] -= new_psc.GCost;
					}
					else {
						for (auto s = new_psc.group[curG].begin(); s != new_psc.group[curG].end(); ++s)
							if(*s != bestSet) delta[*s] -= new_psc.GCost;
					}
				}
				else if (sizeG == 0) {
					for (auto s = new_psc.group[curG].begin(); s != new_psc.group[curG].end(); ++s)
						if(*s != bestSet) delta[*s] += new_psc.GCost;
				}

				// 根据element调整delta
				//auto start2 = std::chrono::high_resolution_clock::now();
				for (auto e = new_psc.coveringSet[idx].begin(); e != new_psc.coveringSet[idx].end(); ++e) {
					int sizeE = visE[*e].size();
					if (sizeE == 2 && BexistX) {
						for (auto s = visE[*e].begin(); s != visE[*e].end(); ++s)
							if (*s != bestSet) delta[*s] -= new_psc.profit[*e];
					}
					else if (sizeE == 1) {
						if (BexistX) {
							for (auto s = e2Set[*e].begin(); s != e2Set[*e].end(); ++s) {
								if (*s == bestSet) continue;
								delta[*s] += new_psc.profit[*e];
							}
						}
						else {
							auto s = visE[*e].begin();
							delta[*s] += new_psc.profit[*e];
						}
					}
					else if (sizeE == 0) {
						for (auto s = e2Set[*e].begin(); s != e2Set[*e].end(); ++s)
							if (*s != bestSet) delta[*s] -= new_psc.profit[*e];
					}
				}
				/*auto end2 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
				times2 += elapsed2.count();*/
				//更改X1
				if (BexistX) { //在当前解中，移出去
					X1.erase(bestSet);
					visG[curG].erase(bestSet);
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						visE[*eid].erase(bestSet);
					}
				}
				else { //不在当前解中，移进来
					X1.insert(bestSet);
					visG[curG].insert(bestSet);
					for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
						visE[*eid].insert(bestSet);
					}
				}
			};
			auto moveSet = [&](SetId curs) {
				bool isInX;
				if (X1.find(curs) == X1.end()) isInX = false;
				else isInX = true;

				delta[curs] = -delta[curs];

				if (isInX) {
					X1.erase(curs);
					//对组进行处理
					int curG = set2G[curs];
					visG[curG].erase(curs);
					int gsize = visG[curG].size();
					if (gsize == 0)
						for (auto s1 = new_psc.group[curG].begin(); s1 != new_psc.group[curG].end(); ++s1) {
							if (*s1 != curs) delta[*s1] -= new_psc.GCost;
						}
					else if (gsize == 1)
						delta[*visG[curG].begin()] += new_psc.GCost;

					//对元素进行处理
					for (auto e = new_psc.coveringSet[curs].begin(); e != new_psc.coveringSet[curs].end(); ++e) {
						visE[*e].erase(curs);
						int vSize = visE[*e].size();
						if (vSize == 0) {
							for (auto s1 = e2Set[*e].begin(); s1 != e2Set[*e].end(); ++s1)
								if (*s1 != curs) delta[*s1] += new_psc.profit[*e];
						}
						else if (vSize == 1) {
							delta[*visE[*e].begin()] -= new_psc.profit[*e];
						}
					}
				}
				else {
					X1.insert(curs);
					//对组进行处理
					int curG = set2G[curs];
					visG[curG].insert(curs);
					int gsize = visG[curG].size();
					if (gsize == 2)
						for (auto s1 = visG[curG].begin(); s1 != visG[curG].end(); ++s1) {
							if (*s1 != curs) delta[*s1] -= new_psc.GCost;
						}
					else if (gsize == 1)
						for (auto s1 = new_psc.group[curG].begin(); s1 != new_psc.group[curG].end(); ++s1)
							if (*s1 != curs) delta[*s1] += new_psc.GCost;

					//对元素进行处理
					for (auto e = new_psc.coveringSet[curs].begin(); e != new_psc.coveringSet[curs].end(); ++e) {
						visE[*e].insert(curs);
						int vSize = visE[*e].size();
						if (vSize == 1)
							for (auto s1 = e2Set[*e].begin(); s1 != e2Set[*e].end(); ++s1) {
								if (*s1 != curs) delta[*s1] -= new_psc.profit[*e];
							}
						else if (vSize == 2)
							for (auto s1 = visE[*e].begin(); s1 != visE[*e].end(); ++s1) {
								if (*s1 != curs) delta[*s1] += new_psc.profit[*e];
							}
					}
				}
			};

			auto flipIn = [&](Sets& tmpX, SetId bestSet, vector<double>& tmpD, vector<unordered_set<SetId>>& tmpG, 
				vector<unordered_set<SetId>>& tmpE) {
				int idx = bestSet;
				// 调整自己的delta
				tmpD[idx] = -tmpD[idx];
				// 根据group调整delta
				int curG = set2G[idx];
				int sizeG = tmpG[curG].size();

				if (sizeG == 0) {
					for (auto s = new_psc.group[curG].begin(); s != new_psc.group[curG].end(); ++s)
						if (*s != bestSet) tmpD[*s] += new_psc.GCost;
				}
				else if (sizeG == 1) {
					auto s = tmpG[curG].begin();
					tmpD[*s] -= new_psc.GCost;
				}

				// 根据element调整delta
				auto start2 = std::chrono::high_resolution_clock::now();
				for (auto e = new_psc.coveringSet[idx].begin(); e != new_psc.coveringSet[idx].end(); ++e) {
					int sizeE = tmpE[*e].size();
					if (sizeE == 0) {
						for (auto s = e2Set[*e].begin(); s != e2Set[*e].end(); ++s)
							if (*s != bestSet) tmpD[*s] -= new_psc.profit[*e];
					}
					else if (sizeE == 1) {
						auto s = tmpE[*e].begin();
						tmpD[*s] += new_psc.profit[*e];
					}
				}
				auto end2 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
				times2 += elapsed2.count();

				tmpX.insert(bestSet);
				tmpG[curG].insert(bestSet);
				for (auto eid = new_psc.coveringSet[bestSet].begin(); eid != new_psc.coveringSet[bestSet].end(); ++eid) {
					tmpE[*eid].insert(bestSet);
				}
			};

			auto flipOut = [&](Sets& tmpX, SetId bestSet, vector<double>& tmpD, vector<unordered_set<SetId>>& tmpG,
				vector<unordered_set<SetId>>& tmpE) {
				int idx = bestSet;

				tmpD[idx] = -tmpD[idx];
				int curG = set2G[idx];

				// 根据group调整delta
				int sizeG = tmpG[curG].size();
				if (sizeG == 2) {
					for (auto s = tmpG[curG].begin(); s != tmpG[curG].end(); ++s)
						if (*s != bestSet) tmpD[*s] += new_psc.GCost;
				}
				else if (sizeG == 1) {
					for (auto s = new_psc.group[curG].begin(); s != new_psc.group[curG].end(); ++s)
						if (*s != bestSet) tmpD[*s] -= new_psc.GCost;
				}

				// 根据element调整delta
				auto start2 = std::chrono::high_resolution_clock::now();
				for (auto e = new_psc.coveringSet[idx].begin(); e != new_psc.coveringSet[idx].end(); ++e) {
					int sizeE = tmpE[*e].size();
					if (sizeE == 2)
						for (auto s = tmpE[*e].begin(); s != tmpE[*e].end(); ++s) {
							if (*s != bestSet) tmpD[*s] -= new_psc.profit[*e];
						}
					else if (sizeE == 1) {
						for (auto s = e2Set[*e].begin(); s != e2Set[*e].end(); ++s) {
							if (*s != bestSet) tmpD[*s] += new_psc.profit[*e];
						}
					}
				}
				auto end2 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
				times2 += elapsed2.count();

				tmpX.erase(bestSet);
				tmpG[curG].erase(bestSet);
				for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid)
					tmpE[*eid].erase(bestSet);
			};

			// 将换入操作和换出操作分开进行呢
			// 先判断换出操作是否可行，不可行直接进行换入操作
			auto FlipTabuSearch = [&](double& f_X1) {
				auto start2 = std::chrono::high_resolution_clock::now();
				// 禁忌表的设计/delta的计算
				vector<int> tabuList(new_psc.setNum, 0);
				int iterCnt = 0, non_improve = 0; //记录迭代轮次和未改进次数
				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisg = visG;
				/*Sets Nx1;
				int flip_outCnt = 0, flip_inCnt = 0;
				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN).first;
					if (X1.find(sid) != X1.end()) continue;
					Nx1.insert(sid);
				}*/
				vector<SetId> vec_set;
				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) 
					vec_set.push_back(*setN);

				while (non_improve < beta && restMilliSec() > 0) {
					iterCnt += 1;
					SetId bestSet, bestSettmp, tmpBest1, tmpBest2;
					/*unordered_set<SetId> bestSet1, bestSet2;*/
					SetId bestSet1 = -1, bestSet2;
					double maxProfit1 = -1e8, maxProfit2 = -1e8, maxProfit = -1e8, maxProfit3 = -1e8;
					// 这里确定禁忌表和特赦准则的问题
					// 禁忌选择的是
					// 1、非禁忌动作的最优值和
					// 2、禁忌动作中最好的能够改进历史结果的值
					// 选择1和2中更好的那个
					auto start7 = std::chrono::high_resolution_clock::now();
					/*for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
						SetId sid = (*setN).first;
						int idx = (*setN).second; 
					
						if (tabuList[idx] < iterCnt && delta[idx] > maxProfit 
						      || tabuList[idx] >= iterCnt && fb < f_X1 + delta[idx] && delta[idx] > maxProfit) {
							bestSet = sid;
							maxProfit = delta[idx];
						}
					}*/

					for (auto setN = vec_set.begin(); setN != vec_set.end(); ++setN) {
						SetId sid = *setN;
						int idx = *setN;

						if (tabuList[idx] < iterCnt || tabuList[idx] >= iterCnt && fb - f_X1 - delta[idx] < -0.0001) {
							if (delta[idx] - maxProfit1 > 0.0001) {
								maxProfit2 = maxProfit1;
								bestSet2 = bestSet1;

								bestSet1 = sid;
								maxProfit1 = delta[idx];
							}
							else if (delta[idx] - maxProfit2 > 0.0001) {
								bestSet2 = sid;
								maxProfit2 = delta[idx];
							}
						}
					}
					if (fastRand(10000) / 10000.0 < 0.6) {
						bestSet = bestSet1;
						maxProfit = maxProfit1;
					}
					else {
						bestSet = bestSet2;
						maxProfit = maxProfit2;
					}

					//for (auto setN = X1.begin(); setN != X1.end(); ++setN) {
					//	int idx = new_psc.SMap[*setN];
					//	if (delta[idx] > maxProfit1 && tabuList[idx] < iterCnt) {
					//		maxProfit1 = delta[idx];
					//		tmpBest1 = *setN;
					//	}
					//	else if (tabuList[idx] >= iterCnt && delta[idx] + f_X1 > fb && delta[idx] > maxProfit1) {
					//		maxProfit1 = delta[idx];
					//		tmpBest1 = *setN;
					//	}
					//}
					//// 若maxProfit1 > 0, 表示可以精简X1，减少元素的冗余覆盖
					//// 若maxProfit1 <= 0, 表示不能精简X1，元素的覆盖率不够
					//if (maxProfit1 <= 0) {
					//	for (auto setN = Nx1.begin(); setN != Nx1.end(); ++setN) {
					//		int idx = new_psc.SMap[*setN];
					//		if (delta[idx] > maxProfit2 && tabuList[idx] < iterCnt) {
					//			maxProfit2 = delta[idx];
					//			tmpBest2 = *setN;
					//		}
					//		else if (tabuList[idx] >= iterCnt && delta[idx] + f_X1 > fb && delta[idx] > maxProfit2) {
					//			maxProfit2 = delta[idx];
					//			tmpBest2 = *setN;
					//		}
					//	}
					//}
					//if (maxProfit1 > 0) {
					//	maxProfit = maxProfit1;
					//	bestSet = tmpBest1;
					//	Nx1.insert(bestSet);
					//}
					//else {
					//	maxProfit = maxProfit2;
					//	bestSet = tmpBest2;
					//	Nx1.erase(bestSet);
					//}
					//f_X1 += maxProfit;


					if (maxProfit == -1e8) continue;
					f_X1 = f_X1 + maxProfit;

					//for (auto setN = Nx1.begin(); setN != Nx1.end(); ++setN) {
					//	/*int idx = new_psc.SMap[*setN];*/
					//	int idx = *setN;
					//	if (delta[idx] > maxProfit2 && tabuList[idx] < iterCnt) {
					//		maxProfit2 = delta[idx];
					//		tmpBest2 = *setN;
					//	}
					//	else if (tabuList[idx] >= iterCnt && delta[idx] > maxProfit2) {
					//		maxProfit2 = delta[idx];
					//		tmpBest2 = *setN;
					//	}
					//}
					////先添加元素，再进行精简 
					//if (maxProfit2 <= 0) {
					//	for (auto setN = X1.begin(); setN != X1.end(); ++setN) {
					//		int idx = new_psc.SMap[*setN];
					//		if (delta[idx] > maxProfit1 && tabuList[idx] < iterCnt) {
					//			maxProfit1 = delta[idx];
					//			tmpBest1 = *setN;
					//		}
					//		else if (tabuList[idx] >= iterCnt && delta[idx] > maxProfit1) {
					//			maxProfit1 = delta[idx];
					//			tmpBest1 = *setN;
					//		}
					//	}
					//}
					//if (maxProfit2 > 0 || maxProfit2 > maxProfit1) {
					//	maxProfit = maxProfit2;
					//	bestSet = tmpBest2;
					//	Nx1.erase(bestSet);
					//}
					//else {
					//	maxProfit = maxProfit1;
					//	bestSet = tmpBest1;
					//    Nx1.insert(bestSet);
					//}
					//f_X1 += maxProfit;
					auto end7 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed7 = end7 - start7;
					times7 += elapsed7.count();

					// 调整δ, 更改X1和TabuList
					auto start2 = std::chrono::high_resolution_clock::now();
					//flip(bestSet);
					moveSet(bestSet);
					auto end2 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
					times2 += elapsed2.count();
					/*auto end2 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
					times2 += elapsed2.count();*/

					if (X1.find(bestSet) != X1.end())
						tabuList[bestSet] = iterCnt + fastRand(1, 6);
					else tabuList[bestSet] = iterCnt + new_psc.SMap.size(); //这个禁忌值偏大了？
					
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
				flipIterCnt += iterCnt;

				
				/*cerr << "第" << iterCnt << "次迭代" << endl;
				int idx = 0;
				for (; idx < visG.size(); ++idx) {
					cerr << "group " << idx << ": " << visG[idx].size() << endl;
				}*/
				

				auto end2 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
				times3 += elapsed2.count();
			};

			//使用δ'，使性能得到提升
			auto SwapDescentSearch = [&](double& f_X1) {
				auto start2 = std::chrono::high_resolution_clock::now();

				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisg = visG;
				vector<SetId> Nx1;
				vector<int> pos_Nx1(psc.setNum, -1);
				vector<double> delta1 = delta;
				unordered_map < SetId, vector<double>> deltas;
				
				int idx = 0;
				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN);
					if (X1.find(sid) == X1.end()) {
						Nx1.push_back(sid);
						pos_Nx1[sid] = idx++;
					}
				}

				int non_improve = 0;
				int iter_cnt = 0;
 				while (non_improve < 1 && restMilliSec() > 0) {
				//while (non_improve < 10 && restMilliSec() > 0) {	
					iter_cnt += 1;
					SetId bestS1, bestS2;
					vector<pair<SetId, SetId>> bestSs;
					double bestdp = -1e8;
					double dsum1 = 0, dsum = 0;

					//选择最佳邻域动作

					//分开进行操作，可以降低时间复杂度，但是性能可能稍差
					
					vector<SetId> bestSs1;
					for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
						if (delta[*s1] > bestdp) {
							bestSs1.clear();
							bestdp = delta[*s1];
							bestSs1.push_back(*s1);
						}
						else if (abs(delta[*s1] - bestdp) < 0.0001) bestSs1.push_back(*s1);
					}
					bestS1 = bestSs1[fastRand(bestSs1.size())];
					dsum = bestdp;
					delta1 = delta;
					int curG = set2G[bestS1];
					//计算组
					if (visG[curG].size() == 1 && (*visG[curG].begin() == bestS1)) {
						for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
							if (*s2 != bestS1)
								delta1[*s2] -= new_psc.GCost;
						}
					}
					//计算元素收益
					for (auto e = new_psc.coveringSet[bestS1].begin(); e != new_psc.coveringSet[bestS1].end(); ++e) {
						if (visE[*e].size() > 1) continue;
						if (*visE[*e].begin() == bestS1) {
							for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2)
								if (*s2 != bestS1)
									delta1[*s2] += new_psc.profit[*e];
						}
					}
					bestdp = -1e8;
					for (auto s2 = Nx1.begin(); s2 != Nx1.end(); ++s2) {
						if (delta1[*s2] > bestdp) {
							bestSs1.clear();
							bestdp = delta1[*s2];
							bestSs1.push_back(*s2);
						}
						else if (abs(delta1[*s2] - bestdp) < 0.0001) bestSs1.push_back(*s2);
					}
					bestS2 = bestSs1[fastRand(bestSs1.size())];
					dsum1 = bestdp;
					bestdp = dsum + dsum1;

					if (bestdp <= 0) {
						bestdp = -1e8;
						dsum = 0;
						dsum1 = 0;
						auto start4 = std::chrono::high_resolution_clock::now();
						for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
							delta1 = delta;
							int curG = set2G[*s1];
							// 计算变化的Δ'的时间是最久的
							//计算组
							if (visG[curG].size() == 1) {
								for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
									if (*s2 != *s1) 
										delta1[*s2] -= new_psc.GCost;		
								}
							}
							//计算元素收益
							//int pftCnt = 0;
							auto start3 = std::chrono::high_resolution_clock::now();
							for (auto e = new_psc.coveringSet[*s1].begin(); e != new_psc.coveringSet[*s1].end(); ++e) {
								if (visE[*e].size() > 1) continue;
								for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2) {
									if (*s2 != *s1) {
										delta1[*s2] += new_psc.profit[*e];
									}	
								}	
							}
							auto end3 = std::chrono::high_resolution_clock::now();
							std::chrono::duration<double, std::milli> elapsed3 = end3 - start3;
							times5 += elapsed3.count();
							
							for (auto s2 = Nx1.begin(); s2 != Nx1.end(); ++s2) {
								dsum = delta1[*s2] + delta[*s1];
								if (dsum > bestdp) {
									bestSs.clear();
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
									bestdp = dsum;
								}
								else if (abs(dsum - bestdp) < 0.0001) bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
								
							}
							// flip(s1, X1, Nx1) ->delta
							/*auto start4 = std::chrono::high_resolution_clock::now();*/
							 
							/*auto end4 = std::chrono::high_resolution_clock::now();
							std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
							times6 += elapsed4.count();*/
						}

						auto end4 = std::chrono::high_resolution_clock::now();
						std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
						times6 += elapsed4.count();
						int sidx = fastRand(bestSs.size());
						bestS1 = bestSs[sidx].first;
						bestS2 = bestSs[sidx].second;
					}

					int len = Nx1.size();
					pos_Nx1[Nx1.back()] = pos_Nx1[bestS2];
					Nx1[pos_Nx1[bestS2]] = Nx1[len - 1];
					Nx1.pop_back();
					Nx1.push_back(bestS1);
					pos_Nx1[bestS1] = len - 1;
					/*Nx1.erase(bestS2);
					Nx1.insert(bestS1);*/

					// 以上动作执行完后，确定 s1，s2为最佳邻域动作，执行这些动作并修改相应的值即可
					
					auto start4 = std::chrono::high_resolution_clock::now();
					/*flip(bestS1);
					flip(bestS2);*/
					moveSet(bestS1);
					moveSet(bestS2);
					/*flipOut(X1, bestS1);
					flipIn(X1, bestS2);*/
					auto end4 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
					times2 += elapsed4.count();

					f_X1 += bestdp;

					if (f_X1 - fb > 0.0001) {
						Xb = X1;
						fb = f_X1;

						tmpDel = delta;
						tmpvise = visE;
						tmpvisg = visG;
						non_improve = 0;
					}
					else non_improve += 1;
				}
				swapIterCnt += iter_cnt;
				X1 = Xb;
				f_X1 = fb;
				delta = tmpDel;
				visG = tmpvisg;
				visE = tmpvise;

				auto end2 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
				times4 += elapsed2.count(); 
			};

			//只使用受到影响的子集进行交换
			auto SwapDescentSearch1 = [&](double& f_X1) {
				auto start2 = std::chrono::high_resolution_clock::now();

				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisg = visG;
				vector<SetId> Nx1;
				vector<int> pos_Nx1(psc.setNum, -1);
				int pos_len = 0;
				vector<double> delta1 = delta;
				unordered_map < SetId, vector<double>> deltas;

				int non_improve = 0;
				int iter_cnt = 0;
				while (non_improve < 1 && restMilliSec() > 0) {
					//while (non_improve < 10 && restMilliSec() > 0) {	
					Nx1.clear();
					fill(pos_Nx1.begin(), pos_Nx1.end(), -1);
					pos_len = 0;

					iter_cnt += 1;
					SetId bestS1, bestS2;
					vector<pair<SetId, SetId>> bestSs;
					double bestdp = -1e8;
					double dsum1 = 0, dsum = 0;

					//选择最佳邻域动作

					//分开进行操作，可以降低时间复杂度，但是性能可能稍差

					vector<SetId> bestSs1;
					for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
						if (delta[*s1] > bestdp) {
							bestSs1.clear();
							bestdp = delta[*s1];
							bestSs1.push_back(*s1);
						}
						else if (abs(delta[*s1] - bestdp) < 0.0001) bestSs1.push_back(*s1);
					}
					bestS1 = bestSs1[fastRand(bestSs1.size())];
					dsum = bestdp;
					delta1 = delta;
					int curG = set2G[bestS1];
					//计算组
					if (visG[curG].size() == 1 && (*visG[curG].begin() == bestS1)) {
						for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
							if (*s2 != bestS1) {
								delta1[*s2] -= new_psc.GCost;
								if (pos_Nx1[*s2] == -1) {
									Nx1.push_back(*s2);
									pos_Nx1[*s2] = pos_len++;
								}
							}	
						}
					}
					//计算元素收益
					for (auto e = new_psc.coveringSet[bestS1].begin(); e != new_psc.coveringSet[bestS1].end(); ++e) {
						if (visE[*e].size() > 1) continue;
						if (*visE[*e].begin() == bestS1) {
							for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2)
								if (*s2 != bestS1) {
									delta1[*s2] += new_psc.profit[*e];
									if (pos_Nx1[*s2] == -1) {
										Nx1.push_back(*s2);
										pos_Nx1[*s2] = pos_len++;
									}
								}	
						}
					}
					bestdp = -1e8;
					for (auto s2 = Nx1.begin(); s2 != Nx1.end(); ++s2) {
						if (delta1[*s2] > bestdp) {
							bestSs1.clear();
							bestdp = delta1[*s2];
							bestSs1.push_back(*s2);
						}
						else if (abs(delta1[*s2] - bestdp) < 0.0001) bestSs1.push_back(*s2);
					}
					bestS2 = bestSs1[fastRand(bestSs1.size())];
					dsum1 = bestdp;
					bestdp = dsum + dsum1;

					if (bestdp <= 0) {
						bestdp = -1e8;
						dsum = 0;
						dsum1 = 0;
						auto start4 = std::chrono::high_resolution_clock::now();
						for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
							delta1 = delta;
							
							Nx1.clear();
							fill(pos_Nx1.begin(), pos_Nx1.end(), -1);
							pos_len = 0;

							int curG = set2G[*s1];
							// 计算变化的Δ'的时间是最久的
							//计算组
							if (visG[curG].size() == 1) {
								for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
									if (*s2 != *s1) {
										delta1[*s2] -= new_psc.GCost;
										if (pos_Nx1[*s2] == -1) {
											Nx1.push_back(*s2);
											pos_Nx1[*s2] = pos_len++;
										}
									}
								}
							}
							//计算元素收益
							//int pftCnt = 0;
							auto start3 = std::chrono::high_resolution_clock::now();
							for (auto e = new_psc.coveringSet[*s1].begin(); e != new_psc.coveringSet[*s1].end(); ++e) {
								if (visE[*e].size() > 1) continue;
								for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2) {
									if (*s2 != *s1) {
										delta1[*s2] += new_psc.profit[*e];
										if (pos_Nx1[*s2] == -1) {
											Nx1.push_back(*s2);
											pos_Nx1[*s2] = pos_len++;
										}
									}
								}
							}
							auto end3 = std::chrono::high_resolution_clock::now();
							std::chrono::duration<double, std::milli> elapsed3 = end3 - start3;
							times5 += elapsed3.count();

							for (auto s2 = Nx1.begin(); s2 != Nx1.end(); ++s2) {
								dsum = delta1[*s2] + delta[*s1];
								if (dsum > bestdp) {
									bestSs.clear();
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
									bestdp = dsum;
								}
								else if (abs(dsum - bestdp) < 0.0001) bestSs.push_back(pair<SetId, SetId>(*s1, *s2));

							}
						}

						auto end4 = std::chrono::high_resolution_clock::now();
						std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
						times6 += elapsed4.count();
						int sidx = fastRand(bestSs.size());
						bestS1 = bestSs[sidx].first;
						bestS2 = bestSs[sidx].second;
					}
					/*Nx1.erase(bestS2);
					Nx1.insert(bestS1);*/

					// 以上动作执行完后，确定 s1，s2为最佳邻域动作，执行这些动作并修改相应的值即可

					auto start4 = std::chrono::high_resolution_clock::now();
					/*flip(bestS1);
					flip(bestS2);*/
					moveSet(bestS1);
					moveSet(bestS2);
					/*flipOut(X1, bestS1);
					flipIn(X1, bestS2);*/
					auto end4 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
					times2 += elapsed4.count();

					f_X1 += bestdp;

					if (f_X1 - fb > 0.0001) {
						Xb = X1;
						fb = f_X1;

						tmpDel = delta;
						tmpvise = visE;
						tmpvisg = visG;
						non_improve = 0;
					}
					else non_improve += 1;
				}
				swapIterCnt += iter_cnt;
				X1 = Xb;
				f_X1 = fb;
				delta = tmpDel;
				visG = tmpvisg;
				visE = tmpvise;

				auto end2 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
				times4 += elapsed2.count();
			};
			//在同一个组内进行交换操作
			auto SwapDescentSearch2 = [&](double& f_X1) {
				auto start3 = std::chrono::high_resolution_clock::now();
				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisg = visG;
				Sets Nx1, tmpX = X1;
				vector<double> delta1 = delta;
				unordered_map < SetId, vector<double>> deltas;
				vector<SetId> TabuList(psc.setNum, 0);
				vector<Sets> Nx_group(new_psc.groupNum), x_group(new_psc.groupNum);

				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN);
					if (X1.find(sid) != X1.end()) continue;
					Nx1.insert(sid);
				}

				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN);
					if (X1.find(sid) != X1.end()) x_group[set2G[sid]].insert(sid);
					else Nx_group[set2G[sid]].insert(sid);
				}

				int non_improve = 0;
				int iter_cnt = 0;
				while (non_improve < 1 && restMilliSec() > 0) {
					iter_cnt += 1;
					double bestdp = -1e8;
					double bestdp1 = bestdp;
					SetId bestS1, bestS2, tmps1, tmps2;
					vector<pair<SetId, SetId>> bestSs, bestSs1;

					auto start4 = std::chrono::high_resolution_clock::now();
					for (int gid = 0; gid < new_psc.groupNum; ++gid) {
						double dsum = 0;

						if (x_group[gid].size() == 0) continue;
						// 先换入，再换出
						/*for (auto s2 = Nx_group[gid].begin(); s2 != Nx_group[gid].end(); ++s2) {
							delta1 = delta;
							int curG = set2G[*s2];
							if (visG[curG].size() == 1) {
								auto s1 = visG[curG].begin();
								delta1[*s1] -= new_psc.GCost;
							}

							for (auto e = new_psc.coveringSet[*s2].begin(); e != new_psc.coveringSet[*s2].end(); ++e) {
								if (visE[*e].size() == 1) {
									auto s1 = visE[*e].begin();
									delta1[*s1] += new_psc.profit[*e];
								}
							}

							for (auto s1 = x_group[gid].begin(); s1 != x_group[gid].end(); ++s1) {
								dsum = delta1[*s1] + delta[*s2];
								if (dsum > bestdp) {
									bestSs.clear();
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
									bestdp = dsum;
								}
								else if (abs(dsum - bestdp) < 0.0001)
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
							}
						}*/
						//cerr << "先换人，再换出" << endl;
						//先换出，再换入
						
						for (auto s1 = x_group[gid].begin(); s1 != x_group[gid].end(); ++s1) {
							delta1 = delta;
							int curG = set2G[*s1];
						
							//计算组
							if (visG[curG].size() == 1) {
								for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2)
									if (*s2 != *s1) delta1[*s2] -= new_psc.GCost;
							}
						
							//计算元素收益
							for (auto e = new_psc.coveringSet[*s1].begin(); e != new_psc.coveringSet[*s1].end(); ++e) {
								if (visE[*e].size() > 1) continue;
								for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2) {
									if (set2G[*s2] != curG) continue;
									if (*s2 != *s1) delta1[*s2] += new_psc.profit[*e];
								}
							}
							for (auto s2 = Nx_group[gid].begin(); s2 != Nx_group[gid].end(); ++s2) {
								dsum = delta1[*s2] + delta[*s1];
								if (dsum > bestdp1) {
									bestSs.clear();
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
									bestdp1 = dsum;
								}
								else if (abs(dsum - bestdp1) < 0.0001)
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
							}
						}
						//cerr << "先换入， 再换出完成" << endl;
					}

					auto end4 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
					times6 += elapsed4.count();
					int sidx = fastRand(bestSs.size());
					bestS1 = bestSs[sidx].first;
					bestS2 = bestSs[sidx].second;
					/*tmps1 = bestSs1[sidx].first;
					tmps2 = bestSs1[sidx].second;
					cerr << tmps1 << " " << tmps2 << endl;
					cerr << bestS1 << " " << bestS2 << endl;*/

					x_group[set2G[bestS1]].erase(bestS1);
					x_group[set2G[bestS1]].insert(bestS2);
					Nx_group[set2G[bestS1]].erase(bestS2);
					Nx_group[set2G[bestS1]].insert(bestS1);

					auto start2 = std::chrono::high_resolution_clock::now();
					/*flip(bestS1);
					flip(bestS2);*/
					moveSet(bestS1);
					moveSet(bestS2);
					auto end2 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;

					f_X1 += bestdp1;

					if (f_X1 - fb > 0.0001) {
						Xb = X1;
						fb = f_X1;
						tmpDel = delta;
						tmpvise = visE;
						tmpvisg = visG;
						non_improve = 0;
					}
					else non_improve += 1;
				}
				swapIterCnt += iter_cnt;

				X1 = Xb;
				f_X1 = fb;
				delta = tmpDel;
				visG = tmpvisg;
				visE = tmpvise;
				//testDelta(X1, new_psc, delta);
				auto end3 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed3 = end3 - start3;
				times4 += elapsed3.count();
			};

			//只在被选中的组中进行交换
			auto SwapDescentSearch3 = [&](double& f_X1) {
				auto start2 = std::chrono::high_resolution_clock::now();

				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisg = visG;
				Sets Nx1;
				vector<double> delta1 = delta;
				unordered_map < SetId, vector<double>> deltas;

				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN);
					if (X1.find(sid) != X1.end()) continue;
					if (visG[set2G[sid]].size() > 0)
						Nx1.insert(sid);
				}

				//cout << "Nx1.size(): " << Nx1.size() << endl;

				int non_improve = 0;
				int iter_cnt = 0;
				while (non_improve < 1 && restMilliSec() > 0) {
					//while (non_improve < 10 && restMilliSec() > 0) {	
					iter_cnt += 1;
					SetId bestS1, bestS2;
					vector<pair<SetId, SetId>> bestSs;
					double bestdp = -1e8;
					double dsum1 = 0, dsum = 0;

					//选择最佳邻域动作

					//分开进行操作，可以降低时间复杂度，但是性能可能稍差
					vector<SetId> bestSs1;
					for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
						if (delta[*s1] > bestdp) {
							bestSs1.clear();
							bestdp = delta[*s1];
							bestSs1.push_back(*s1);
						}
						else if (abs(delta[*s1] - bestdp) < 0.0001) bestSs1.push_back(*s1);
					}
					bestS1 = bestSs1[fastRand(bestSs1.size())];
					dsum = bestdp;
					delta1 = delta;
					int curG = set2G[bestS1];
					//计算组
					if (visG[curG].size() == 1 && (*visG[curG].begin() == bestS1)) {
						for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
							if (*s2 != bestS1)
								delta1[*s2] -= new_psc.GCost;
						}
					}
					//计算元素收益
					for (auto e = new_psc.coveringSet[bestS1].begin(); e != new_psc.coveringSet[bestS1].end(); ++e) {
						if (visE[*e].size() > 1) continue;
						if (*visE[*e].begin() == bestS1) {
							for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2)
								if (*s2 != bestS1)
									delta1[*s2] += new_psc.profit[*e];
						}
					}
					bestdp = -1e8;
					for (auto s2 = Nx1.begin(); s2 != Nx1.end(); ++s2) {
						if (delta1[*s2] > bestdp) {
							bestSs1.clear();
							bestdp = delta1[*s2];
							bestSs1.push_back(*s2);
						}
						else if (abs(delta1[*s2] - bestdp) < 0.0001) bestSs1.push_back(*s2);
					}
					bestS2 = bestSs1[fastRand(bestSs1.size())];
					dsum1 = bestdp;
					bestdp = dsum + dsum1;

					if (bestdp <= 0) {
						bestdp = -1e8;
						dsum = 0;
						dsum1 = 0;
						auto start4 = std::chrono::high_resolution_clock::now();

						for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
							delta1 = delta;
							int curG = set2G[*s1];
							// 计算变化的Δ'的时间是最久的
							//计算组
							if (visG[curG].size() == 1 && (*visG[curG].begin() == *s1)) {
								for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
									if (*s2 != *s1)
										delta1[*s2] -= new_psc.GCost;
								}
							}
							//计算元素收益
							//int pftCnt = 0;
							auto start3 = std::chrono::high_resolution_clock::now();
							for (auto e = new_psc.coveringSet[*s1].begin(); e != new_psc.coveringSet[*s1].end(); ++e) {
								if (visE[*e].size() > 1) continue;
								for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2) {
									if (*s2 != *s1)
										delta1[*s2] += new_psc.profit[*e];
								}
							}
						
							auto end3 = std::chrono::high_resolution_clock::now();
							std::chrono::duration<double, std::milli> elapsed3 = end3 - start3;
							times5 += elapsed3.count();
						
							for (auto s2 = Nx1.begin(); s2 != Nx1.end(); ++s2) {
								dsum = delta1[*s2] + delta[*s1];
								if (dsum > bestdp) {
									bestSs.clear();
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
									bestdp = dsum;
								}
								else if (abs(dsum - bestdp) < 0.0001) bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
							}
						}

						/*for (auto s2 = Nx1.begin(); s2 != Nx1.end(); ++s2) {
							delta1 = delta;
							int curG = set2G[*s2];

							auto start3 = std::chrono::high_resolution_clock::now();
							if (visG[curG].size() == 1)
								delta1[*visG[curG].begin()] -= psc.GCost;
							for (auto e = new_psc.coveringSet[*s2].begin(); e != new_psc.coveringSet[*s2].end(); ++e) {
								if (visE[*e].size() == 1)
									delta1[*visE[*e].begin()] += new_psc.profit[*e];
							}
							auto end3 = std::chrono::high_resolution_clock::now();
							std::chrono::duration<double, std::milli> elapsed3 = end3 - start3;
							times5 += elapsed3.count();


							for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
								dsum = delta[*s2] + delta1[*s1];
								if (dsum > bestdp) {
									bestSs.clear();
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
									bestdp = dsum;
								}
								else if (abs(dsum - bestdp) < 0.0001) bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
							}

						}*/

						auto end4 = std::chrono::high_resolution_clock::now();
						std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
						times6 += elapsed4.count();
						int sidx = fastRand(bestSs.size());
						bestS1 = bestSs[sidx].first;
						bestS2 = bestSs[sidx].second;
					}

					// 以上动作执行完后，确定 s1，s2为最佳邻域动作，执行这些动作并修改相应的值即可

					auto start4 = std::chrono::high_resolution_clock::now();
					flip(bestS1);
					flip(bestS2);
					Nx1.erase(bestS2);
					if (visG[set2G[bestS1]].size() > 0)
						Nx1.insert(bestS1);
					/*flipOut(X1, bestS1);
					flipIn(X1, bestS2);*/
					auto end4 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
					times2 += elapsed4.count();

					f_X1 += bestdp;

					if (f_X1 - fb > 0.0001) {
						Xb = X1;
						fb = f_X1;

						tmpDel = delta;
						tmpvise = visE;
						tmpvisg = visG;
						non_improve = 0;
					}
					else non_improve += 1;
				}
				swapIterCnt += iter_cnt;
				X1 = Xb;
				f_X1 = fb;
				delta = tmpDel;
				visG = tmpvisg;
				visE = tmpvise;

				auto end2 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
				times4 += elapsed2.count();
			};

			auto R_swapOut = [&](vector<double>& delta1, int R, double& dsum, vector<unordered_set<SetId>>& tmpG,
				vector<unordered_set<SetId>>& tmpE) {
				SetId bestS1, bestS2;
				vector<SetId> bestS1s;
				vector<pair<SetId, SetId>> bestSs;
				double bestdp = -1e8;
				vector<SetId> bestSs1;
				Sets tmpX = X1;

				for (int i = 1; i <= R; ++i) {
					bestSs1.clear();
					bestdp = -1e8;
					for (auto s1 = tmpX.begin(); s1 != tmpX.end(); ++s1) {
						if (delta1[*s1] > bestdp) {
							bestSs1.clear();
							bestdp = delta1[*s1];
							bestSs1.push_back(*s1);
						}
						else if (abs(delta1[*s1] - bestdp) < 0.0001) bestSs1.push_back(*s1);
					}
					
					bestS1 = bestSs1[fastRand(bestSs1.size())];
					bestS1s.push_back(bestS1);
					dsum += bestdp;
					flipOut(tmpX, bestS1, delta1, tmpG, tmpE);
				}
				return bestS1s;
			};

			auto R_swapIn = [&](vector<double>& delta1, int R, double& dsum1, Sets Nx1, vector<unordered_set<SetId>>& tmpG,
				vector<unordered_set<SetId>>& tmpE) {
				Sets tmpNx1 = Nx1;
				SetId bestS2;
				vector<SetId> bestS2s;
				vector<SetId> bestSs1;
				double bestdp = -1e8; 
				for (int i = 1; i <= R; ++i) {
					bestSs1.clear();
					bestdp = -1e8;
					for (auto s2 = tmpNx1.begin(); s2 != tmpNx1.end(); ++s2) {
						if (delta1[*s2] > bestdp) {
							bestSs1.clear();
							bestdp = delta1[*s2];
							bestSs1.push_back(*s2);
						}
						else if (abs(delta1[*s2] - bestdp) < 0.0001) bestSs1.push_back(*s2);
					}
					bestS2 = bestSs1[fastRand(bestSs1.size())];
					bestS2s.push_back(bestS2);
					dsum1 += bestdp;
					tmpNx1.erase(bestS2);

					if (i < R) {
						//计算组
						int curG = set2G[bestS2];
						tmpG[curG].insert(bestS2);
						if (tmpG[curG].size() == 1)
							for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
								if ((*s2) != bestS2) delta1[*s2] += new_psc.GCost;
							}
						//计算元素
						for (auto e = new_psc.coveringSet[bestS2].begin(); e != new_psc.coveringSet[bestS2].end(); ++e) {
							tmpE[*e].insert(bestS2);
							if (tmpE[*e].size() == 1)
								for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2)
									if ((*s2) != bestS2) delta1[*s2] -= new_psc.profit[*e];
						}
					}
				}
				return bestS2s;
			};

			auto SwapDescentSearch4 = [&](double& f_X1) {
				auto start2 = std::chrono::high_resolution_clock::now();
				int R = 1;
				Sets Xb = X1;
				double fb = f_X1;
				vector<double> tmpDel = delta;
				vector<unordered_set<SetId>> tmpvise = visE;
				vector<unordered_set<SetId>> tmpvisg = visG;
				Sets Nx1;
				vector<double> delta1;

				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN);
					if (X1.find(sid) != X1.end()) continue;
					Nx1.insert(sid);
				}

				int non_improve = 0;
				int iter_cnt = 0;

				while (non_improve < 1 && restMilliSec() > 0) {
					iter_cnt += 1;
					SetId bestS1, bestS2;
					vector<SetId> bestS1s, bestS2s;
					vector<pair<SetId, SetId>> bestSs;
					vector<SetId> bestSs1;
					Sets tmpNx1 = Nx1;
					vector<unordered_set<SetId>> tmpG, tmpE;
					double bestdp = -1e8;
					double dsum1, dsum;
					R = 1;
					for (; R <= 3; R++) {
						delta1 = delta;
						dsum = 0;
						dsum1 = 0;
						tmpG = visG;
						tmpE = visE;

						bestS1s = R_swapOut(delta1, R, dsum, tmpG, tmpE);
						bestS2s = R_swapIn(delta1, R, dsum1, Nx1, tmpG, tmpE);

						bestdp = dsum + dsum1;
						if (bestdp > 0) break;
					}
					
					if (bestdp <= 0) {
						bestS1s.clear();
						bestS2s.clear();
						bestdp = -1e8;
						dsum = 0;
						dsum1 = 0;
						auto start4 = std::chrono::high_resolution_clock::now();
						for (auto s1 = X1.begin(); s1 != X1.end(); ++s1) {
							delta1 = delta;
							int curG = set2G[*s1];
							// 计算变化的Δ'的时间是最久的
							//计算组
							if (visG[curG].size() == 1) {
								for (auto s2 = new_psc.group[curG].begin(); s2 != new_psc.group[curG].end(); ++s2) {
									if (*s2 != *s1)
										delta1[*s2] -= new_psc.GCost;
								}
							}
							//计算元素收益
							//int pftCnt = 0;
							auto start3 = std::chrono::high_resolution_clock::now();
							for (auto e = new_psc.coveringSet[*s1].begin(); e != new_psc.coveringSet[*s1].end(); ++e) {
								if (visE[*e].size() > 1) continue;
								for (auto s2 = e2Set[*e].begin(); s2 != e2Set[*e].end(); ++s2) {
									if (*s2 != *s1) {
										delta1[*s2] += new_psc.profit[*e];
									}
								}
							}

							auto end3 = std::chrono::high_resolution_clock::now();
							std::chrono::duration<double, std::milli> elapsed3 = end3 - start3;
							times5 += elapsed3.count();

							for (auto s2 = Nx1.begin(); s2 != Nx1.end(); ++s2) {
								dsum = delta1[*s2] + delta[*s1];
								if (dsum > bestdp) {
									bestSs.clear();
									bestSs.push_back(pair<SetId, SetId>(*s1, *s2));
									bestdp = dsum;
								}
								else if (abs(dsum - bestdp) < 0.0001) bestSs.push_back(pair<SetId, SetId>(*s1, *s2));

							}
						}

						auto end4 = std::chrono::high_resolution_clock::now();
						std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
						times6 += elapsed4.count();
						int sidx = fastRand(bestSs.size());
						bestS1 = bestSs[sidx].first;
						bestS2 = bestSs[sidx].second;
						bestS1s.push_back(bestS1);
						bestS2s.push_back(bestS2);
					}

					auto start4 = std::chrono::high_resolution_clock::now();

					for (auto tmps2 = bestS2s.begin(); tmps2 != bestS2s.end(); ++tmps2) {
						Nx1.erase(*tmps2);
						moveSet(*tmps2);
					}
					for (auto tmps1 = bestS1s.begin(); tmps1 != bestS1s.end(); ++tmps1) {
						Nx1.insert(*tmps1);
						moveSet(*tmps1);
					}
					
					auto end4 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed4 = end4 - start4;
					times2 += elapsed4.count();

					f_X1 += bestdp;


					if (f_X1 - fb > 0.0001) {
						Xb = X1;
						fb = f_X1;

						tmpDel = delta;
						tmpvise = visE;
						tmpvisg = visG;
						non_improve = 0;
					}
					else non_improve += 1;
				}
				swapIterCnt += iter_cnt;
				X1 = Xb;
				f_X1 = fb;
				delta = tmpDel;
				visG = tmpvisg;
				visE = tmpvise;

				auto end2 = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
				times4 += elapsed2.count();
			};

			// 似乎扰动不是很合理，可以进行处理
			auto Perturbation1 = [&](double& f_tmpX) {
				Sets tmpX2 = X1;
				unordered_set<SetId> Ns;
				unordered_set<SetId> tmpSM;
				for (auto s = new_psc.SMap.begin(); s != new_psc.SMap.end(); ++s)
					tmpSM.insert(*s);
				int rmv_n = 0;
				for (auto s = tmpX2.begin(); s != tmpX2.end(); ++s) {
					double isDel = fastRand(10000) / 10000.0;
					if (isDel < 0.3) {
						f_tmpX += delta[*s];
						flip(*s);
						rmv_n += 1;
					}
				}
				for (int i = 0; i < rmv_n; ++i) {
					
					int len = tmpSM.size();
					auto s = next(tmpSM.begin(), fastRand(len));
					SetId sid = (*s);
					if (tmpX2.find(sid) == tmpX2.end()) {
						f_tmpX += delta[sid];
						flip(sid);
					}
					tmpSM.erase(sid);
				}
			};

			auto Perturbation2 = [&](double& f_tmpX) {
				Sets tmpX2 = X1;
				unordered_set<int> Z, Nz; //Z表示 组中的覆盖集与X的交集不为空的组序号
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
					auto cg = next(Z.begin(), idx); // cg为选出的组
					int icg = *cg;
					auto tmpG = visG[icg];
					for (auto s = tmpG.begin(); s != tmpG.end(); ++s) {
						f_tmpX += delta[*s];
						flip(*s);
					}
					Z.erase(icg);
				}

				for (int i = 0; i < tochs; ++i) {
					int len = Nz.size();
					if (Nz.size() == 0) {
						//cerr << "扰动部分的问题! " << endl;
						break;
					}
					int idx = fastRand(len);
					auto cg = next(Nz.begin(), idx);
					int icg = *cg;
					Nz.erase(icg);

					int fcnt = tmpX2.size() / Zlen;
					auto tmpg = new_psc.group[icg];
					for (int j = 0; j < fcnt; ++j) {
						int idx = fastRand(tmpg.size());
						auto it = next(tmpg.begin(), idx);
						SetId s = *it;
						tmpg.erase(s);
						/*tmpX.insert(s);*/
						f_tmpX += delta[s];
						flip(s);
					}
				}
			};

			auto Perturbation = [&](int& t_type, double& f_tmpX) {
				if (fastRand(10000) / 10000.0 < gamma[0]) {
					// 执行Set_Pertubation
					t_type = 0;
					Perturbation1(f_tmpX);
				}
				else {
					// 执行Group_Pertubation
					t_type = 1;
					Perturbation2(f_tmpX);
				}
			};

			auto TwoPhaseLS = [&](double& f_X1)   {
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
					//在这里添加关于子集的扰动
					//Perturbation1(X1, f_X1);

					iter_cnt += 1;
					non_improve = 1; 
					
					FlipTabuSearch(f_X1);
					
					/*cerr << "after exe Tabu" << endl;
					bool testDel1 = testDelta(X1, new_psc, delta);*/

					//start2 = std::chrono::high_resolution_clock::now();
					SwapDescentSearch(f_X1);
					//SwapDescentSearch1(f_X1);
					//SwapDescentSearch2(f_X1);
					//SwapDescentSearch3(f_X1);
					//SwapDescentSearch4(f_X1);
					/*end2 = std::chrono::high_resolution_clock::now();
					elapsed2 = end2 - start2;
					times4 += elapsed2.count();*/
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
				tot_iterCnt += iter_cnt;
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

			auto IntensifivationDrivenILS = [&](Sets input, double& f_X0) {
				auto start = std::chrono::high_resolution_clock::now();

				Sets tmpX = input;
				X1 = input;
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
					//auto start2 = std::chrono::high_resolution_clock::now();
					TwoPhaseLS(fp);
					/*auto end2 = std::chrono::high_resolution_clock::now();
					std::chrono::duration<double, std::milli> elapsed2 = end2 - start2;
					times += elapsed2.count();*/
					//cerr << elapsed2.count() / 1000.0 << endl;

					/*cout << endl << iter_cnt << "th iteration " << endl;
					for (int idx = 0; idx < new_psc.groupNum; ++idx) {
						if (visG[idx].size() > 0) {
							cout << endl << idx + 1 << "th group, sets are: ";
							for (auto s = visG[idx].begin(); s != visG[idx].end(); ++s)
								cout << *s << " ";
							cout << endl;
						}
					}*/

					if (abs(fp - tmp_f) < 0.0001 || fp < tmp_f) non_improve += 1;
					else {
						// 更新γ 
						if (t_type == 0) d1 += 1;
						else if (t_type == 1) d2 += 1;
						gamma[0] = (d0 + d1) / (2 * d0 + d1 + d2); 
						gamma[1] = 1 - gamma[0];
						cerr << "gamma0: " << gamma[0] << endl;

						// 更新eta
						for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
							int j = (*setN);
							SetId sid = (*setN);
							double phi1 = 0.2, phi2 = 0.3, phi3 = 0.3; 
							double alpha = 0.90;
							bool existX0 = X1.find(sid) != X1.end(), existBX = tmpX.find(sid) != tmpX.end();
							if (existX0 && existBX) eta[j] = phi1 + (1 - phi1) * eta[j];
							else if (existX0 && (!existBX)) eta[j] = phi2 + (1 - phi2) * eta[j];
							else if ((!existX0) && existBX) eta[j] = (1 - phi2) * eta[j];
							else eta[j] = (1 - phi1) * eta[j];
							// 进行平滑操作
							if (eta[j] > alpha) eta[j] = (1 - phi3) * eta[j];
							else if (eta[j] < 1 - alpha) eta[j] = phi3 + (1 - phi3) * eta[j];
						
						}

						tmpX = X1;
						tmp_f = fp;
						tmpDel = delta;
						tmpvise = visE;
						tmpvisG = visG;
						non_improve = 0; 
						cerr << "current best result: " << tmp_f << endl;
						cerr << "d1: " << d1 << "; d2: " << d2 << endl;

						for (int idx = 0; idx < new_psc.groupNum; ++idx) {
							if (visG[idx].size() > 0) {
								cout << endl << idx + 1 << "th group, sets are: ";
								for (auto s = visG[idx].begin(); s != visG[idx].end(); ++s)
									cout << *s << " ";
								cout << endl;
							}
						}

						cerr << "number of IILS iteration: " << iter_cnt << endl;
						cerr << "time of executing TwoPhaseLS: " << times / 1000.0 << " s" << endl;
						cerr << "time of executing flip: " << times2 / 1000.0 << " s" << endl;
						cerr << "time of executing Tabu Search's finding best move: " << times7 / 1000.0 << " s" << endl;
						cerr << "time of executing Tabu Search: " << times3 / 1000.0 << " s" << endl;
						cerr << "time of executing Swap Search: " << times4 / 1000.0 << " s" << endl << endl;
						cerr << "cal time of Swap Search's Δ': " << times5 / 1000.0 << " s" << endl;
						cerr << "time of dual search of Swap Search: " << times6 / 1000.0 << " s" << endl;
					}
					
					X1 = tmpX;
					fp = tmp_f;
					visE = tmpvise;
					visG = tmpvisG;
					delta = tmpDel;
					//judgeVis(visE, visG, Xp, new_psc);
					Perturbation(t_type, fp);
					//Perturbation1(Xp, fp);
	
				}
				cerr << "number of executing IntensifivationDrivenILS: " << iter_cnt << endl;
				f_X0 = tmp_f;

				cerr << "time of executing TwoPhaseLS: " << times / 1000.0 << " s" << endl;
				cerr << "time of executing flip: " << times2 / 1000.0 << " s" << endl;
				cerr << "time of executing Tabu Search: " << times3 / 1000.0 << " s" << endl;
				cerr << "number of Tabu Search iteration: " << flipIterCnt << endl;
				cerr << "time of executing Swap Search: " << times4 / 1000.0 << " s" << endl;
				cerr << "cal time of Swap Search's Δ': " << times5 / 1000.0 << " s" << endl;
				cerr << "time of dual search of Swap Search: " << times6 / 1000.0 << " s" << endl;
				cout << "number of swap descent search: " << swapIterCnt << endl;
				//cout << "number of calpft > choose: " << pftIterCnt << endl;

				/*times = 0;
				times2 = 0;
				times3 = 0;
				times4 = 0;
				times5 = 0;
				times6 = 0;
				times7 = 0;*/
				auto end = std::chrono::high_resolution_clock::now();
				std::chrono::duration<double, std::milli> elapsed = end - start;
				std::cout << "Elapsed time: " << elapsed.count() / 1000.0 << " s" << std::endl;

				return tmpX;
			};

			Sets pre_X0;
			int restart_cnt = 0;
			while (restMilliSec() > 0) {
				// 获得初始解后，要确定δ向量和初始解的收益值，即f_X0
				double f_X0 = 0;

				X0 = LearningDrivenInitialization1();   

				restart_cnt += 1;

				cout << "solution init finished" << endl;
				// 计算收益值和visG、visE
				for (ElemId eid = 0; eid < new_psc.elemNum; ++eid)
					visE[eid].clear();
				for (int gid = 0; gid < new_psc.groupNum; ++gid)
					visG[gid].clear();
				f_X0 = calProfit(X0, new_psc, set2G, visE, visG);

				// 计算δ函数
				fill(delta.begin(), delta.end(), 0);
				for (auto s = X0.begin(); s != X0.end(); ++s) {
					visG[set2G[*s]].insert(*s);
					for (auto eid = new_psc.coveringSet[*s].begin(); eid != new_psc.coveringSet[*s].end(); ++eid)
						visE[*eid].insert(*s);
				}

				for (auto setN = new_psc.SMap.begin(); setN != new_psc.SMap.end(); ++setN) {
					SetId sid = (*setN);
					int idx = (*setN);
					// 当前覆盖集位于初始解中
					if (X0.find(sid) != X0.end()) {
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
							if (visE[*eid].size() == 1) delta[idx] -= new_psc.profit[*eid];
						}
						delta[idx] += new_psc.SCost[idx];
						if (visG[set2G[idx]].size() == 1) delta[idx] += new_psc.GCost;
					}
					else { //当前覆盖集不在初始解中
						for (auto eid = new_psc.coveringSet[idx].begin(); eid != new_psc.coveringSet[idx].end(); ++eid) {
							if (visE[*eid].size() == 0) delta[idx] += new_psc.profit[*eid];
						}
						delta[idx] -= new_psc.SCost[idx];
						if (visG[set2G[idx]].size() == 0) delta[idx] -= new_psc.GCost;
					}
				}
				
				cout << "profit before IFD is: " << f_X0 << endl;
				
				X0 = IntensifivationDrivenILS(X0, f_X0);

				/*double testf = calProfit(X0, new_psc);
				if (testf - f_X0 >= 0.00001 || testf - f_X0 <= -0.00001) {
					cerr << "increment error! " << endl;
					cerr << "realf :" << testf << " f_X0: " << f_X0 << endl;
				}*/
				
				// 确定当前解与之前得到的解的相似度
				/*int sameCnt = 0;
				if (pre_X0.size() > 0) {
					for (auto s = X0.begin(); s != X0.end(); ++s) {
						if (pre_X0.find(*s) != pre_X0.end()) sameCnt += 1;
					}
					cout << "the same of previous solution: " << sameCnt / (double)pre_X0.size() << endl;
				}
				pre_X0 = X0;*/

				
				if (f_X0 > best_f) {
					best_X = X0;
					best_f = f_X0;
				} 
				cout << "size of current solution: " << best_X.size() << endl;
				cout << "current max profit: " << best_f << endl << endl;

				//vector<unordered_set<SetId>> tmpvisE(new_psc.elemNum), tmpvisG(new_psc.groupNum);
				//for (auto s = X0.begin(); s != X0.end(); ++s) {
				//	tmpvisG[set2G[*s]].insert(*s);
				//	for (auto eid = new_psc.coveringSet[*s].begin(); eid != new_psc.coveringSet[*s].end(); ++eid)
				//		tmpvisE[*eid].insert(*s);
				//}
				//visE = tmpvisE;
				//visG = tmpvisG;
				////reduceGroup(X0);
				//
				//int cnt = 0, cnt0 = 0;
				//for (auto e = tmpvisE.begin(); e != tmpvisE.end(); ++e) {
				//	if ((*e).size() == 1) cnt += 1;
				//	if ((*e).size() == 0) cnt0 += 1;
				//}
				//cout << "the number of elements covered by one subset: " << cnt << endl;
				//cout << "the number of uncovered elements: " << cnt0 << endl;
				//cout << "sum of elements: " << new_psc.elemNum << endl << endl;
			}
			for (ElemId eid = 0; eid < new_psc.elemNum; ++eid)
				visE[eid].clear();
			for (int gid = 0; gid < new_psc.groupNum; ++gid)
				visG[gid].clear();
			double real_f = calProfit(best_X, new_psc, set2G, visE, visG);
			cout << "real max profit: " << real_f << endl;
			cout << "increment profit: " << best_f << endl;
			cout << "number of flip Tabu Search: " << flipIterCnt << endl;
			cout << "number of swap descent search: " << swapIterCnt << endl;
			cout << "number of TwoPhaseLS iteration: " << tot_iterCnt << endl;
			cout << "number of restart times: " << restart_cnt << endl;
			/*vector<unordered_set<SetId>> tmpvisE(new_psc.elemNum), tmpvisG(new_psc.groupNum);
			for (auto s = best_X.begin(); s != best_X.end(); ++s) {
				tmpvisG[set2G[*s]].insert(*s);
				for (auto eid = new_psc.coveringSet[*s].begin(); eid != new_psc.coveringSet[*s].end(); ++eid)
					tmpvisE[*eid].insert(*s);
			}
			visE = tmpvisE;
			visG = tmpvisG;
			reduceGroup(best_X);
			real_f = calProfit(best_X, new_psc);
			cout << "profit after reducing group: " << real_f << endl;*/

			/*vector<int> groupSet(new_psc.groupNum, 0);
			for (auto s = best_X.begin(); s != best_X.end(); ++s) {
				groupSet[set2G[*s]] += 1;
			}
			for (int i = 0; i < groupSet.size(); ++i) {
				cerr << groupSet[i] << endl;
			}*/
			return best_f;
		}
	};

	double solvePMForSetCovering(Sets& output, PSetCovering& input, std::function<long long()> restMilliSec, int seed) {
		return Solver().solve(output, input, restMilliSec, seed);
	}
	void calRatio(PSetCovering input, string testFile) {
		Solver().CoveringRate(input, testFile);
	}
	void calCoveredRatio(PSetCovering input, string testFile) {
		Solver().CoveredRate(input, testFile);
	}

	void calElement2Group(PSetCovering input) {
		Solver().element2Group(input);
	}
}

