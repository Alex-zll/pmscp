#pragma once

#ifndef PROFIT_MAXIMIZATION_FOR_SET_COVERING_PROBLEM_H
#define PROFIT_MAXIMIZATION_FOR_SET_COVERING_PROBLEM_H

/*
	该问题中，包含了三类数据结构：
	  1、由所有元素(elements/blocks)构成的集合，在这个集合中，有元素的id和收益

	  2、由部分元素构成的覆盖集(set/drill hole)，包含了能够覆盖到的元素id及该覆盖集的成本

	  3、由部分覆盖集构成的组(group)，包含了位于同一组的若干覆盖集 及 该组的成本

	该问题的解：包含了若干覆盖集使得总收益最大
*/

/*
	说明：可能不能使用矩阵u来确定元素ei属于哪些覆盖集（会导致内存超限），矩阵v也是同理，不去使用

	一些需要用到的数据结构：
		1、三个 一维数组，来确定元素(element)、覆盖集(covering_set)、组(group)是否已经被选择，利用这三个数组可以对目标函数进行计算
		2、
*/

#include<vector>
#include<unordered_set>
#include<functional>
#include <unordered_map>

namespace pmscp {
	using ElemId = int;
	using SetId = int;
	using Money = double;
	using Elems = std::unordered_set<ElemId>;
	using Sets = std::unordered_set<SetId>;
	using CSet = std::unordered_map<SetId, int>; //SetId所在coveringSet的位置

	struct PSetCovering {
		int elemNum;
		int groupNum;
		int setNum;
		Money GCost;
		CSet SMap; //SetId所在coveringSet的位置
		std::vector<Money> profit; //profit[i]表示 元素i的收益值
		std::vector<Elems> coveringSet; //coveringSet[i]表示 覆盖集i可以覆盖到的元素
		std::vector<Money> SCost; //SCost[i]表示 覆盖集i的成本
		std::vector<Sets> group; // group[i]表示 组别i所包含的覆盖集
	};  

	double solvePMForSetCovering(Sets& output, PSetCovering& input, std::function<long long()> restMilliSec, int seed);
}


#endif // !PROFIT_MAXIMIZATION_FOR_SET_COVERING_PROBLEM_H

