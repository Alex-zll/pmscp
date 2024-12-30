#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <chrono>
#include <ctime>
#include <thread>
#include <Windows.h>

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
					elms.push_back(eid);
					psc.profit[eid] = ep;
				}
				else {
					cerr << "Error: '|' not found in token " << token << endl;
				}
			}
			psc.coveringSet.push_back(elms);
			//psc.SMap[sid] = sid;
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
		std::cerr << "open file error：" << fileName << std::endl;
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

	std::cout << "data append success" << std::endl;

}

void test(string path, long long secTimeout) {
	PSetCovering psc;
	cerr << "loading input " << endl;
	loadInput(path, psc);
	Sets X;
	double result;
	steady_clock::time_point endTime = steady_clock::now() + seconds(secTimeout);

	size_t last_slash_idx = path.find_last_of("/");
	string testFile = path.substr(last_slash_idx + 1);
	//calRatio(psc, testFile);
	//calCoveredRatio(psc, testFile);
	cerr << "solving problem " << endl;
	result = solvePMForSetCovering(X, psc, [&]() { return duration_cast<milliseconds>(endTime - steady_clock::now()).count(); }, 1735180925);
	//calElement2Group(psc);
}

void test(string path, long long secTimeout, int seed, string fileName) {
	PSetCovering psc;
	cerr << "loading input " << endl;
	loadInput(path, psc);
	Sets X;
	double result;
	steady_clock::time_point endTime = steady_clock::now() + seconds(secTimeout);
	size_t last_slash_idx = path.find_last_of("\\");
	if (last_slash_idx == string::npos) last_slash_idx = path.find_last_of("/");
	string testFile = path.substr(last_slash_idx + 1);

	cerr << "solving problem " << endl;
	result = solvePMForSetCovering(X, psc, [&]() { return duration_cast<milliseconds>(endTime - steady_clock::now()).count(); }, seed);
	saveToCSV(fileName, testFile, seed, result);
}

int main(int argc, char* argv[]) {
	if (argc < 2) {
		string loadFile = "D:/0HustWork/hust-exercise/PMSCP_data/PMSCP-main/instances1/B5.txt";
		long long secTimeout = 1500;
		test(loadFile, secTimeout);
	}
	else {
		string loadFile = argv[1];
		auto now = chrono::system_clock::now();
		int seed = static_cast<int>(chrono::system_clock::to_time_t(now));
		int secTimeout = atoi(argv[2]);
		string fileName = argv[3];

		test(loadFile, secTimeout, seed, fileName);
	}

	return 0;
}

//扰动可以再试试别的想法

//swap可以接受差解
//只对受到影响子集的做交换

//先尝试只对受到影响的子集做交换
//再尝试swap可以接受差解，把扰动去掉