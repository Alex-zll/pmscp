#pragma once

#ifndef PROFIT_MAXIMIZATION_FOR_SET_COVERING_PROBLEM_H
#define PROFIT_MAXIMIZATION_FOR_SET_COVERING_PROBLEM_H

/*
	�������У��������������ݽṹ��
	  1��������Ԫ��(elements/blocks)���ɵļ��ϣ�����������У���Ԫ�ص�id������

	  2���ɲ���Ԫ�ع��ɵĸ��Ǽ�(set/drill hole)���������ܹ����ǵ���Ԫ��id���ø��Ǽ��ĳɱ�

	  3���ɲ��ָ��Ǽ����ɵ���(group)��������λ��ͬһ������ɸ��Ǽ� �� ����ĳɱ�

	������Ľ⣺���������ɸ��Ǽ�ʹ�����������
*/

/*
	˵�������ܲ���ʹ�þ���u��ȷ��Ԫ��ei������Щ���Ǽ����ᵼ���ڴ泬�ޣ�������vҲ��ͬ����ȥʹ��

	һЩ��Ҫ�õ������ݽṹ��
		1������ һά���飬��ȷ��Ԫ��(element)�����Ǽ�(covering_set)����(group)�Ƿ��Ѿ���ѡ������������������Զ�Ŀ�꺯�����м���
		2��
*/

#include<vector>
#include<unordered_set>
#include<functional>
#include <unordered_map>
#include <string>

namespace pmscp {
	using ElemId = int;
	using SetId = int;
	using Money = double;
	using Elems = std::vector<ElemId>;
	using Sets = std::unordered_set<SetId>;
	using Svec = std::vector<SetId>; //SetId����coveringSet��λ��

	struct PSetCovering {
		int elemNum;
		int groupNum;
		int setNum;
		Money GCost;
		Svec SMap; //SetId����coveringSet��λ��
		std::vector<Money> profit; //profit[i]��ʾ Ԫ��i������ֵ
		std::vector<Elems> coveringSet; //coveringSet[i]��ʾ ���Ǽ�i���Ը��ǵ���Ԫ��
		std::vector<Money> SCost; //SCost[i]��ʾ ���Ǽ�i�ĳɱ�
		std::vector<Sets> group; // group[i]��ʾ ���i�������ĸ��Ǽ�
	};  

	double solvePMForSetCovering(Sets& output, PSetCovering& input, std::function<long long()> restMilliSec, int seed);
	void calRatio(PSetCovering input, std::string testFile);
	void calCoveredRatio(PSetCovering input, std::string testFile);
	void calElement2Group(PSetCovering input);
}


#endif // !PROFIT_MAXIMIZATION_FOR_SET_COVERING_PROBLEM_H

// �������Ŷ����⻹�Ǿֲ����������⣿
// �Ŷ�����С���������ֻص�֮ǰ�ľֲ�������
// �ֲ������Ĺ�������ʲôϸ���ϵ����⣿

//���Գ��Դ�δ�����ǵ�Ԫ���У��ҵ���������Ԫ�أ�Ȼ��ӿ��Ը������Ԫ�ص��Ӽ������ѡһ��

