#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <chrono>

#include "pmscp.h"

using namespace std;
using namespace std::chrono;
using namespace pmscp;

void loadInput(string loadFile, PSetCovering& psc) {
	ifstream file(loadFile);
	int line_cnt = 0;
	string line;
	int sid = 0;
	while (getline(file, line)) {
		// 前3行分别读取 groupCost、groupNum、elementNum
		// 后m行读取coveringSet的内容和每个element的profit
		string strNum;
		if (line_cnt == 0) {
			auto pos = line.find('=');
			strNum = line.substr(pos + 1);
			double mon = stod(strNum);
			psc.GCost = mon;
		}
		else if (line_cnt == 1) {
			auto pos = line.find('=');
			strNum = line.substr(pos + 1);

			psc.elemNum = stoi(strNum);
			psc.profit.resize(psc.elemNum);
		}
		else if (line_cnt == 2) {
			auto pos = line.find('=');
			strNum = line.substr(pos + 1);

			int gNum = stoi(strNum);
			psc.groupNum = gNum;
			psc.group.resize(gNum);
		}
		else {
			istringstream iss(line);
			string token;
			
			for (int i = 0; i < 7; ++i) iss >> token;
			iss >> token;
			psc.SCost.push_back(stod(token));
			iss >> token;
			int gid = stoi(token);
			psc.group[gid].insert(sid);
			Elems elms;

			while (iss >> token) {
				auto pos = token.find('|');
				if (pos != string::npos) {
					string firstPartString = token.substr(0, pos); // 第一部分字符串
					string secondPartString = token.substr(pos + 1); // 第二部分字符串

					// 转换类型并存储
					ElemId eid = std::stoi(firstPartString);
					Money ep = std::stod(secondPartString);
					elms.insert(eid);
					psc.profit[eid] = ep;
				}
				else {
					cerr << "Error: '|' not found in token " << token << endl;
				}
			}
			psc.coveringSet.push_back(elms);
			psc.SMap[sid] = sid;
			sid++;
		}

		line_cnt++;
	}
	psc.setNum = sid;
}

void saveOutput(string outputFile, PSetCovering psc, Sets X) {

}

void saveToCSV(string fileName, string testFile, int seed, double result) {
	// 打开文件以追加内容
	std::ofstream outfile;
	outfile.open(fileName, std::ios::app); // 使用 ios::app 进行追加

	// 检查文件是否成功打开
	if (!outfile.is_open()) {
		std::cerr << "无法打开文件：" << fileName << std::endl;
		return ;
	}

	// 如果文件是新创建的，先写入标题头
	/*if (outfile.tellp() == std::ofstream::pos_type(0)) {
		outfile << "随机数,算例,结果\n";
	}*/

	// 追加随机数、文件名和结果到文件
	outfile << seed << "," << testFile << "," << result << "\n";

	// 关闭文件流
	outfile.close();

	std::cout << "数据追加写入完成" << std::endl;

}

void test(string path, long long secTimeout) {
	PSetCovering psc;
	cerr << "loading input " << endl;
	loadInput(path, psc);
	Sets X;
	double result;
	steady_clock::time_point endTime = steady_clock::now() + seconds(secTimeout);
	cerr << "solving problem " << endl;
	result = solvePMForSetCovering(X, psc, [&]() { return duration_cast<milliseconds>(endTime - steady_clock::now()).count(); }, 56635765);

}

void test(string path, long long secTimeout, int seed) {
	PSetCovering psc;
	cerr << "loading input " << endl;
	loadInput(path, psc);
	Sets X;
	double result;
	steady_clock::time_point endTime = steady_clock::now() + seconds(secTimeout);
	cerr << "solving problem " << endl;
	result = solvePMForSetCovering(X, psc, [&]() { return duration_cast<milliseconds>(endTime - steady_clock::now()).count(); }, seed);

	string fileName = "D:/0HustWork/hust-exercise/PMSCP/result.csv";
	size_t last_slash_idx = path.find_last_of("/");
	string testFile = path.substr(last_slash_idx + 1);
	saveToCSV(fileName, testFile, seed, result);
}

int main(int argc, char* argv[]) {
	if (argc < 2) {
		string loadFile = "D:/0HustWork/hust-exercise/PMSCP_data/PMSCP-main/instances1/A1.txt";
		long long secTimeout = 800;
		test(loadFile, secTimeout);
	}
	else {
		string loadFile = argv[1];
		int seed = atoi(argv[2]);
		int secTimeout = atoi(argv[3]);

		test(loadFile, secTimeout, seed);
	}
	


	return 0;
}

// 56635765这个算例算不出来150386