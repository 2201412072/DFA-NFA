#include<iostream>
#include<fstream>
#include<map>
#include<vector>
#include<cstring>
#include<queue>
#include<bitset> 
#include<set>
#define len_nfa 64//初始nfa状态个数最大值 
#define Maxx_dfa 100//中间过程的dfa和最终dfa状态个数最大值 
#define side_nfa 300//初始nfa边的个数最大值 
#define alphabet 128//字符表最大值 
#define maxx_define_num 100//用宏定义语句的最大值 
#define maxx_single_def 100//每条宏定义语句内能够定义的字符数量的最大值 
using namespace std;
//给定自动机状态，生成c++代码
/*
目前的语法： 
#define 来定义宏 eg：#define digit a-zA-Z;
#priority或#pri 定义优先级 eg： #pri  1  2;表示1的优先级为2，优先级越高越优先 
如果没有指定，但构造DFA时出现了两个同等优先级的比较，报出错误，然后按照序号最小的优先级最高继续进行处理 
epsilon表示空串 字符储存为128 
digit等词需要长度至少大于2 
from number;
to number;
来定义初始节点和中止节点; 
其他参照正则表达式 eg： a-e //但不加[]因为那样c++等需要用[的没法弄 
注释为//或/ ** /(这个先不弄) 
正式语法为 from  to  符号  ；
 符号之间用空格隔开，表示或 //define阶段也用 
 //转移字符用\打在前面 
*/ 

/* 
梳理：
1、词法分析：
	name_define记录define的值 
2、初始nfa：
	num_line记录nfa边数 
	from记录入口
	to[]记录出口
	next，front，last记录dfa边，为链式前向星
	NFA记录了每条边含有的字符 
3、epsilon闭包
	bit_epsilon记录闭包
4、mid_dfa
	count_dfa记录mid_dfa节点数
	m_DFA记录了mid_dfa的边，为邻接矩阵 
	bit记录了每个mid_dfa状态中含有的nfa状态 
4、pri
	pri_num记录nfa节点优先级
	pri_dfa记录mid_dfa终止节点及对应输出 
5、hopcroft
	from记录了最终的dfa的开始状态 
	count_h_dfa记录了最终的dfa的状态数 
	belong_dfa记录了每个mid_dfa状态属于哪个最终的dfa状态 
	final_to记录最终的dfa接受状态及对应输出
	final_DFA记录了最终的dfa的边连接方式，本质为邻接矩阵 
*/
//def来记录name_define 
struct def{
	int c[maxx_single_def];//256以内是正常的，256以外，如257表示 name_define[1]里面的内容 
	int num=0;//c的长度，c记录了define定义的字符 
};
struct node{
	int from,to;//起止节点 
	bool operator <(const node &t)const
	{
		if(from!=t.from) return from<t.from;
		if(to!=t.to) return to<t.to;
	}
};
struct bit_dfa{
	bitset<len_nfa> b;
	bool operator <(const bit_dfa &t) const
	{
		//return b.count()<t.b.count();
		int i;
		for(i=len_nfa-1;i>=0;i--)
		{
			if(b[i]==t.b[i]) continue;
			else return b[i]<t.b[i];
		}
		return 0; 
	}
};

FILE *fp; 
char *file_name,*output,*array;
//-----词法分析------
//(from还作用于final_from的记录，to还用于pri_error） 
//flag用于词法分析阶段 
int flag_from=0,flag_define=0,flag_fu=0,flag_to=0,flag_sen=0;
int flag_end=0,flag_pri=0,flag_fenhao=0,flag_ceshi;
/*
flag_fu含义
1：a-Z这种，需要循环处理
2：正常单个字符
3：\t这种转义字符 
*/
//记录from出现了几次 
int num_from=0;
//cnt表示name_define的长度，c_store用于提取token，from起点 
//在hopcrft后from就表示最终的dfa的from 
int cnt=0,c_store=-1,from=-1;
//p_to表示终点个数，n表示代码中最大的状态数 
int p_to=0,n;
//temp_pri用于再词法分析时储存优先级的第一个输入节点
int temp_pri; 
//to表示终点,它是记录了to的编号 
int to[len_nfa];
//记录NFA的临时变量 
node point;
//define产生式 
def name_define[maxx_define_num];
//记录define产生式的名字，给其分配值 
map<string, int> mapp; 

//-----求epsilon闭包------- 
//element记录所有代码中出现的状态 
bool element[len_nfa*3];
//bit_epsilon用于记录x的epsilon闭包，其中第i位代表i个节点 
bitset<len_nfa> bit_epsilon[len_nfa]; 

//------NFA转换为DFA----- 
//（zifu还用于hop_next） 
//字符记录代码中用到的所有字符
set<int> zifu;
//num_line表示NFA生成式的个数
int num_line=0;
//用于生成NFA的有向图 
int next[side_nfa],front[len_nfa],last[side_nfa];
//记录NFA产生式中的字符(改成bitset) 
//它接受nfa一条边的编号，来记录这条边上的字符 
bitset<alphabet+1> NFA[side_nfa];
//count_dfa表示dfa节点的个数 
int count_dfa=0;
//m_DFA表示mid_DFA，是中间过程，
//m_DFA[i][c]表示dfa第i个编号能通过字符c到达哪个节点 
int m_DFA[Maxx_dfa][alphabet];
//好像没法用n,其中第i位代表i个节点,表示产生的dfa中状态包含的nfa 
bitset<len_nfa> bit[Maxx_dfa];

//----pri_error------
//pri_num用于定义各个节点的优先级，初始默认为0 
int pri_num[len_nfa];
//pri_dfa用于记录每个dfa终点节点的要对应的nfa节点 
//pri_dfa就顺便记录了终止节点了，因为有优先级的肯定是终止时的 
int pri_dfa[Maxx_dfa]; 

//-----hopcroft以及hop_next------ 
//final_to表示最终的dfa的终点，它记录了每个节点是否是终点,以及如果是，该输出什么 
int final_to[Maxx_dfa];
//final_DFA[i][c]表示dfa第i个编号能通过字符c到达哪个
int final_DFA[Maxx_dfa][alphabet]; 
//count_h_dfa记录hopcroft后节点个数 
int count_h_dfa=0; 
//belong_dfa记录mid_dfa中哪几个节点属于final_dfa的哪个节点 
int belong_dfa[Maxx_dfa];

string get_token()
{
	string temp="";
	int c;
	flag_end=0;
	flag_fu=2;
	flag_fenhao=0;
	if(c_store==-1)
	{
		c=fgetc(fp);
	}
	else
	{
		c=c_store;
		c_store=-1;
	}
	while(temp==""&&c!=EOF)
	{
		while(c!='\r'&&c!=EOF&&c!='\t'&&c!='\n'&&c!=' ')
		{
			if(c==';'&&temp!="")
			{
				if(!flag_fenhao)//尝试记录“;”但不知道能行不 
				{
					c_store=c;
					flag_end=1;
					break;
				}
				else
				{
					flag_fenhao=0;
				}
			}
			if(c=='\\')
			{
				if(flag_fu==1)
				{
					cout<<"[ERROR]输入字符格式错误"<<endl;
				}
				flag_fu=3;
				flag_fenhao=1;
			}
			else if(c=='-')
			{
				if(flag_fu==3)
				{
					cout<<"[ERROR]输入字符格式错误"<<endl;
				}
				flag_fu=1;
			}
			temp.push_back(c);
			c=fgetc(fp);
		}
		if(!flag_end)
		{
			c=fgetc(fp);
			c_store=c;
		}
	}
	return temp;
}
void deal();//输出 
void add(int *c,int &num,int x);//计算define时用 
void add(bitset<alphabet+1> &b,int x);//将define加入c中 ，计算NFA时用 
void add(int x,int y);//加边(此处边数是从1开始,而其他全从0开始，因为好像初始代码只支持1开始） 
void analyse(int *c,int &num,string token);//计算define时用 
void analyse(bitset<alphabet+1> &b,string token);//计算NFA时用 
void find_set_epsilon(int x);//寻找epsilon闭包 
void NFAtoDFA();
void pri_error();//查看优先级是否发生冲突 
void hopcroft();
void hop_next();//负责处理hopcroft后连边以及from，to和其他东西
void write_dfa_array();//负责写final_dfa数组以及final_from和final_to数组 
void write_code(); //负责写代码 
int toint(string str)
{
	int i,ans=0;
	for(i=0;i<str.length();i++)
	{
		if(str[i]>='0'&&str[i]<='9')
		{
			ans*=10;
			ans+=str[i]-'0';
		}
		else
		{
			return -1;
		}
	}
	return ans;
}
int main()
{
	file_name="自动机程序_LR.txt";
	int len=strlen(file_name);
	output=new char[len+4];
	array=new char[len+6];
	strcpy(output,file_name);
	strcpy(array,file_name);
	output[len-4]='_',output[len-3]='d';
	output[len-2]='f',output[len-1]='a';
	output[len]='.',output[len+1]='t';
	output[len+2]='x',output[len+3]='t';
	array[len-4]='_',array[len-3]='a',array[len-2]='r';
	array[len-1]='r',array[len]='a',array[len+1]='y';
	array[len+2]='.',array[len+3]='t',array[len+4]='x';
	array[len+5]='t';
	//cout<<output<<endl; 
	fp=fopen(file_name,"r");
	string token=get_token();
	for(int i=0;i<side_nfa;i++)
	{
		next[i]=-1;
	}
	for(int i=0;i<Maxx_dfa;i++)
	{
		next[i]=belong_dfa[i]=pri_dfa[i]=final_to[i]=-1;
		for(int j=0;j<alphabet;j++)
		{
			final_DFA[i][j]=-1;
			m_DFA[i][j]=-1;
		}
	}
	while(token!="")
	{
		//cout<<token<<endl;
		if(token=="#define")
		{
			flag_define=1;
			token=get_token();
			continue;
		}
		if(token==";")
		{
			if(flag_sen==2)
			{
				deal();
				num_line++;
				add(point.from,point.to);
			}
			flag_define=0;
			flag_sen=0;
			flag_from=0;
			flag_to=0;
			flag_pri=0;
			token=get_token();
			continue;
		}
		if(token=="from")
		{
			num_from++;
			if(num_from>=2)
			{
				cout<<"[ERROR]定义了太多的from状态"<<endl;
			}
			flag_from=1;
			token=get_token();
			continue;
		}
		if(token=="to")
		{
			flag_to=1;
			token=get_token();
			continue;
		}
		if(token=="#priority"||token=="#pri")
		{
			flag_pri=1;
			token=get_token();
			continue;
		} 
		if(flag_from==1)
		{
			flag_from=0;
			from=toint(token);
			if(from==-1)
			{
				cout<<"[ERROR]from状态必须为一个整数"<<endl;
			}
			else if(from>=len_nfa)
			{
				cout<<"[ERROR]状态定义过大，可以修改程序中的len_nfa值"<<endl;
			} 
			flag_from=-1;
			token=get_token();
			continue;
		}
		
		if(flag_to==1)
		{
			flag_to=0;
			to[p_to]=toint(token);
			if(to[p_to]==-1)
			{
				cout<<"[ERROR]to状态必须为一个整数"<<endl;
			}
			else if(to[p_to]>=len_nfa)
			{
				cout<<"[ERROR]状态定义过大，可以修改程序中的len_nfa值"<<endl;
			} 
			p_to++;
			if(p_to>=len_nfa)
			{
				cout<<"[ERROR]定义的to状态过多，可以修改程序中的len_nfa值"<<endl;
			}
			token=get_token();
			continue;
		}
		
		if(flag_define==1)
		{
			flag_define=2;
			if(token.length()==1)
			{
				cout<<"[ERROR]define中宏名长度至少应为2，否则无法与单字符区分"<<endl;
			}
			cnt++;
			if(cnt>=maxx_define_num) 
			{
				cout<<"[ERROR]定义的define过多，可以修改程序中maxx_define_num的值"<<endl;
			}
			mapp[token]=cnt;
			token=get_token();
			continue;
		}
		else if(flag_define==2||flag_define==3)
		{
			flag_define=3;
			analyse(name_define[cnt].c,name_define[cnt].num,token);
			token=get_token();
			continue;
		}
		if(flag_pri==1)
		{
			temp_pri=toint(token);
			if(temp_pri>=len_nfa)
			{
				cout<<"[ERROR]状态定义过大，可以修改程序中的len_nfa值"<<endl;
			}
			flag_pri=2;
			token=get_token();
			continue;
		}
		else if(flag_pri==2)
		{
			int temp=toint(token);
			if(temp<0)
			{
				cout<<"[ERROR]优先级不能为负"<<endl;
			 } 
			pri_num[temp_pri]=temp;
		}
		if(flag_sen==0)
		{
			
			point.from=toint(token);
			n=n>point.from?n:point.from;
			if(n>=len_nfa)
			{
				cout<<"[ERROR]状态定义过大，可以修改程序中的len_nfa值"<<endl;
			} 
			element[point.from]=1;
			flag_sen=1;
			token=get_token();
			continue;
		}
		else if(flag_sen==1)
		{
			point.to=toint(token);
			n=n>point.to?n:point.to;
			if(n>=len_nfa)
			{
				cout<<"[ERROR]状态定义过大，可以修改程序中的len_nfa值"<<endl;
			}
			element[point.to]=1;
			flag_sen=2;
			token=get_token();
			continue;
		}
		else if(flag_sen==2)
		{
			analyse(NFA[num_line],token);
			token=get_token();
			continue;
		}
		else
		{
			cout<<"[ERROR]无法识别该符号"<<endl;
		 } 
	}
	for(int i=0;i<=n;i++)
	{
		if(element[i])
		{
			find_set_epsilon(i);
		}
	}
	//输出每个节点的epsilon闭包，以bitset形式 
	cout<<"epsilon:"<<endl;
	for(int i=0;i<=n;i++)
	{
		cout<<bit_epsilon[i]<<endl;
	}/**/
	NFAtoDFA();
	//输出mid_DFA的每个状态所包含的nfa的状态 
	cout<<"bit:"<<endl;
	for(int i=0;i<count_dfa;i++)
	{
		//cout<<bit[i]<<endl;
		cout<<i<<":\t";
		for(int j=0;j<len_nfa;j++)
		{
			if(bit[i][j])
			{
				cout<<j<<" ";
			}
		}
		cout<<endl;
		
	}/**/
	//输出mid_DFA的节点以及它识别的字符和能到达的节点 
	cout<<"m_DFA:"<<endl;
	for(int i=0;i<count_dfa;i++)
	{
		cout<<i<<":"<<endl;
		for(int j=0;j<128;j++)
		{
			if(m_DFA[i][j]!=-1)
			{
				cout<<(char)j<<":"<<m_DFA[i][j]<<" ";
			}
		}
		cout<<endl;
	} /**/
	pri_error();
	//输出终点编号以及优先级 
	cout<<"pri_dfa:"<<endl;
	for(int i=0;i<count_dfa;i++)
	{
		if(pri_dfa[i])
		{
			cout<<i<<":"<<pri_dfa[i]<<endl;
		}
	}/**/
	hopcroft();
	hop_next(); 
	cout<<"belong_DFA:"<<endl;
	for(int i=0;i<count_dfa;i++)
	{
		cout<<belong_dfa[i]<<" ";
	}
	cout<<endl;/**/
	set<int>::iterator iter=zifu.begin(); 
	cout<<"final_DFA:"<<endl;
	for(int i=0;i<count_h_dfa;i++)
	{
		cout<<i<<":"<<endl;
		for(iter=zifu.begin();iter!=zifu.end();iter++)
		{
			if(final_DFA[i][*iter]!=-1)
			cout<<(char)*iter<<":"<<final_DFA[i][*iter]<<" ";
		}
		cout<<endl;
	}/**/
	cout<<"final_to:"<<endl;
	for(int i=0;i<count_h_dfa;i++)
	{
		if(final_to[i])
		{
			cout<<i<<":"<<final_to[i]<<endl;
		}
	}/**/
	write_dfa_array();
	write_code(); 
} 
 void analyse(int *c,int &num,string token)
 {
 	int len=token.length();
			if(len==1)
			{
				c[num]=token[0];
				num++;
			}
			else if(len==2)
			{
				if(flag_fu==3)
				{
					c[num]=token[1];
					num++;
				}
				else
				{
					if(mapp.count(token)==0)
					{
						//error;
						cout<<"[ERROR]符号 "<<token<<" 不存在"<<endl;
					}
					else
					{
						add(c,num,mapp[token]);
					}
				}
			}
			else if(len==3)
			{
				if(flag_fu==1)
				{
					for(int i=token[0];i<=token[2];i++)
					{
						c[num]=i;
						num++;
					}
				}
				else
				{
					if(mapp.count(token)==0)
					{
						//error;
						cout<<"[ERROR]符号 "<<token<<" 不存在"<<endl;
					}
					else
					{
						add(c,num,mapp[token]);
					}
				}
			}
			else
			{
				if(token=="epsilon")
				{
					c[num]=128;
					num++;
				 } 
				 else if(mapp.count(token)==0)
				{
					//error;
					cout<<"[ERROR]符号 "<<token<<" 不存在"<<endl;
				}
				else
				{
					add(c,num,mapp[token]);
				}
			}
}
void analyse(bitset<alphabet+1> &b,string token)
{
	int len=token.length();
	if(len==1)
	{
		b.set(token[0]);
		zifu.insert(token[0]);
	}
	else if(len==2)
	{
		if(flag_fu==3)
		{
			b.set(token[1]);
			zifu.insert(token[1]);
		}
		else
		{
			if(mapp.count(token)==0)
			{
				//error;
				cout<<"[ERROR]符号 "<<token<<" 不存在"<<endl;
			}
			else
			{
				add(b,mapp[token]);
			}
		}
	}
	else if(len==3)
	{
		if(flag_fu==1)
		{
			for(int i=token[0];i<=token[2];i++)
			{
				b.set(i);
				zifu.insert(i);
			}
		}
		else
		{
			if(mapp.count(token)==0)
			{
				//error;
				cout<<"[ERROR]符号 "<<token<<" 不存在"<<endl;
			}
			else
			{
				add(b,mapp[token]);
			}
		}
	 }
	else
	{
		if(token=="epsilon")
		{
			b.set(128);
		}
		else if(mapp.count(token)==0)
		{
			//error
			cout<<"[ERROR]符号 "<<token<<" 不存在"<<endl;
		}
		else
		{
			add(b,mapp[token]);
		}
	} 
		
}
 void deal()
 {
 	
 	cout<<point.from<<" "<<point.to<<" "<<endl;
 	for(int i=1;i<=alphabet;i++)
 	{
 		if(NFA[num_line][i])
 		cout<<(char)i<<" ";
	 }
	 cout<<endl;
 }
void add(int *c,int &num,int x)
{
	int i;
	for(i=0;i<name_define[x].num;i++)
	{
		if(name_define[x].c[i]<=alphabet)
 		{
 			c[num]=name_define[x].c[i];
 			num++;
		}
		 else
		 {
		 	add(c,num,name_define[x].c[i]-256);
		 }
	}
}
void add(bitset<alphabet+1> &b,int x)
{
	int i;
	for(i=0;i<name_define[x].num;i++)
	{
		if(name_define[x].c[i]<=alphabet)
		{
			b.set(name_define[x].c[i]);
			if(name_define[x].c[i]<alphabet) 
			zifu.insert(name_define[x].c[i]);
		}
		else
		{
			add(b,name_define[x].c[i]-256);
		}
	}
} 

void add(int x,int y)
{
	last[num_line]=front[x];
	front[x]=num_line;
	next[num_line]=y;
}

void find_set_epsilon(int x)
{
	int k;
	//temp_NFA用于求epsilon闭包 
	bool temp_NFA[len_nfa];
	queue<int>q;
	q.push(x);
	memset(temp_NFA,0,sizeof(temp_NFA));
	temp_NFA[x]=1;
	while(!q.empty())
	{
		int top=q.front();
		q.pop();
		for(k=front[top];next[k]!=-1;k=last[k])
		{
			if(!temp_NFA[next[k]]&&NFA[k-1][128])
			{
				temp_NFA[next[k]]=1;
				q.push(next[k]);
			}
		}
	}
	for(int i=0;i<=n;i++)
	{
		if(temp_NFA[i])
		{
			bit_epsilon[x].set(i);
			//bit_epsilon用于记录x的epsilon闭包，其中第i位代表i-1个节点 
		}	
	}
}
void NFAtoDFA()
{
	//用于给bitset排序，所以加了一个比较bitset的方法 
	flag_ceshi=1;
	map<bit_dfa,int> map_bit;
	queue<bitset<len_nfa> >q;//记录NFAepsilon集合 
	//bitset<128> bit_temp;//记录字符
	queue<int> bianhao; 
	bitset<len_nfa> bit_temp;
	bit_dfa temp;
	temp.b=bit[count_dfa]=bit_epsilon[from];
	map_bit[temp]=0;
	count_dfa++;
	q.push(bit[0]);
	bianhao.push(0);
	while(!q.empty())
	{
		bitset<len_nfa> top_b=q.front();
		int top_bianhao=bianhao.front();
		q.pop();
		bianhao.pop();
		
		set<int>::iterator iter=zifu.begin();
		for(;iter!=zifu.end();iter++)
		{
			bit_temp.reset();
			for(int i=0;i<=n;i++)
			{
				if(top_b[i])
				{
					int k;
					for(k=front[i];k>0&&next[k]!=-1;k=last[k])
					{
						if(NFA[k-1][*iter])
						{
							bit_temp|=bit_epsilon[next[k]];
							//cout<<bit_temp<<endl;
						}
					}
				}
			}
			if(!bit_temp.any()) continue;
			temp.b=bit_temp;
			if(map_bit.count(temp)==0)
			{
				q.push(bit_temp);
				bianhao.push(count_dfa);
				bit[count_dfa]=bit_temp;
				m_DFA[top_bianhao][*iter]=count_dfa;
				map_bit[temp]=count_dfa;
				count_dfa++;
				if(count_dfa>=Maxx_dfa)
				{
					cout<<"[ERROR]转换成的dfa状态过多，可以修改程序的Maxx_dfa的值"<<endl;
				 } 
			}
			else
			{
				int state=map_bit[temp];
				m_DFA[top_bianhao][*iter]=state;
			}
		}
	}
}
void pri_error()
{
	int i,j,k,last_node,maxx=0,count_num=1;
	bitset<len_nfa> b,temp;
	//error_pri记录了错误的优先级nfa节点 
	vector<int> error_pri;
	for(i=0;i<p_to;i++)
	{
		b.set(to[i]);
	}
	for(i=0;i<count_dfa;i++)
	{
		temp=bit[i]&b;
		error_pri.clear();
		maxx=0;
		count_num=1;
		if(temp.count()==0)
		{
			continue;
		}
		else if(temp.count()==1)
		{
			for(j=0;j<=n;j++)
			{
				if(temp[j])
				{
					last_node=j;
					break;
				}
			}
			pri_dfa[i]=last_node;
			continue;
		}
		for(j=0;j<=n;j++)
		{
			if(temp[j])
			{
				if(maxx<pri_num[j])
				{
					maxx=pri_num[j];
					error_pri.clear(); 
					last_node=j;
					count_num=1;
				}
				else if(maxx==pri_num[j])
				{
					count_num++;
					last_node=j;
					error_pri.push_back(j);
				}
			}
		}
		if(count_num>1)
		{
			//error;
			cout<<"[ERROR]未定义"; 
			cout<<error_pri[0];
			for(j=1;j<error_pri.size();j++)
			{
				cout<<","<<error_pri[j];
			}
			cout<<"之间的优先级，导致结果产生二义性。"<<endl;
		}
		pri_dfa[i]=last_node; 
	}
}
void hopcroft()
{
	count_h_dfa=0;
	map<int,int> map_temp_dfa;
	map<int,int> map_temp_hop;
	/*
	record用于记录目前通过第几个字符分割的，因为主要是分割
	N集，所以它们都是从一个集合中分割来的，如果它的父集合
	分割字符从c开始，那么它产生的子集合没必要再去查a和b，它
	无法进行分割。 
	*/ 
	int record[Maxx_dfa],temp,belong_temp[Maxx_dfa];
	queue<int> q;
	for(int i=0;i<count_dfa;i++)
	{
		{
			if(!map_temp_dfa.count(pri_dfa[i]))
			{
				map_temp_dfa[pri_dfa[i]]=count_h_dfa;
				belong_dfa[i]=count_h_dfa;
				count_h_dfa++;
				if(count_h_dfa>=Maxx_dfa)
				{
					cout<<"[ERROR]转换成的dfa状态过多，可以修改程序的Maxx_dfa的值"<<endl;
				 } 
			}
			else
			{
				belong_dfa[i]=map_temp_dfa[pri_dfa[i]];
			}
		}
	}
	for(int i=0;i<count_h_dfa;i++)
	{
		q.push(i);
	}
	memset(record,0,sizeof(record));
	while(!q.empty())
	{
		int top=q.front(),size=0;
		q.pop();
		for(int i=0;i<count_dfa;i++)
		{
			if(belong_dfa[i]==top) size++;
		}
		if(size==1) continue;
		for(int k=record[top];k<alphabet;k++)
		{
			map_temp_hop.clear();
			memset(belong_temp,-1,sizeof(belong_temp));
			size=0;
			for(int j=0;j<count_dfa;j++)
			{
				if(belong_dfa[j]!=top) continue;
				if(m_DFA[j][k]==-1) temp=-1;
				else
					temp=belong_dfa[m_DFA[j][k]];
				if(!map_temp_hop.count(temp))
				{
					if(size==0)
					{
						map_temp_hop[temp]=top;
						size++;
					}
					
					else
					{
						map_temp_hop[temp]=count_h_dfa;
						count_h_dfa++;
						if(count_h_dfa>=Maxx_dfa)
						{
							cout<<"[ERROR]转换成的dfa状态过多，可以修改程序的Maxx_dfa的值"<<endl;
				 		}
						size++;
					}
				}
			}
			if(size==1) continue;
			else
			{
				for(int j=0;j<count_dfa;j++)
				{
					if(belong_dfa[j]!=top) continue;
					if(m_DFA[j][k]==-1) temp=-1;
					else temp=belong_dfa[m_DFA[j][k]];
					belong_temp[j]=map_temp_hop[temp];
					record[j]=k;
				}
				for(int j=0;j<count_dfa;j++)
				{
					if(belong_temp[j]!=-1)
					{
						belong_dfa[j]=belong_temp[j];
					}
				}
				map<int,int>::iterator iter=map_temp_hop.begin();
				for(;iter!=map_temp_hop.end();iter++)
				{
					q.push(iter->second);
				}
				break;
			}
		}
	}
}
void hop_next()//负责处理hopcroft后连边以及from，to和其他东西 
{
	from=belong_dfa[0];
	for(int i=0;i<count_dfa;i++)
	{
		set<int>::iterator iter=zifu.begin();
		for(;iter!=zifu.end();iter++)
		{
			if(m_DFA[i][*iter]!=-1)
			{
				final_DFA[belong_dfa[i]][*iter]=belong_dfa[m_DFA[i][*iter]];
			}
		}
		if(pri_dfa[i]!=-1)
		{
			final_to[belong_dfa[i]]=pri_dfa[i]; 
		}
	}
}
//目前有用的final_DFA邻接矩阵，count_h_dfa节点个数，
//from起点，final_to终点以及需要的输出
void write_dfa_array()
{
	ofstream mycout;
	mycout.open(array,ios::out|ios::trunc);
	int i;
	mycout<<count_h_dfa<<endl;
	for(i=0;i<count_h_dfa;i++)
	{
		for(int j=0;j<alphabet;j++)
		{
			mycout<<final_DFA[i][j]<<" ";//final_DFA如无边则为-1 
		}
		mycout<<endl;
	}
	mycout<<from<<endl;//写final_from 
	for(i=0;i<count_h_dfa;i++)//写final_to 
	{
		mycout<<final_to[i]<<" ";//final_to如不为to则为-1 
	}
	mycout.close();
} 
void write_code()
{
	ofstream mycout;
	mycout.open(output,ios::out|ios::trunc);
	ifstream mycin(array);
	int i;
	mycout<<"#include<fstream>"<<endl;
	mycout<<"#include<stack>"<<endl;
	mycout<<"#include<queue>"<<endl;
	mycout<<"int state;//state代表当前状态"<<endl;
	mycout<<"struct dfa_result_node{"<<endl;
	mycout<<"	int result,indicator;"<<endl;
	mycout<<"};"<<endl;
	mycout<<"queue<dfa_result_node> dfa_result;//dfa_result代表目前识别出来的结果"<<endl;
	mycout<<"int dfa_array["<<count_h_dfa<<"]["<<alphabet<<"];"<<endl;
	mycout<<"int count_dfa;//count_dfa代表dfa的状态个数"<<endl;
	mycout<<"int dfa_to["<<count_h_dfa<<"],dfa_from;//dfa_to代表某个状态是否为接受状态，以及如是应输出什么"<<endl;
	mycout<<"int dfa_init()"<<endl<<"{"<<endl;
	mycout<<'\t'<<"int i,j;"<<endl<<'\t';
	mycout<<"ifstream mycin(\""<<array<<"\");"<<endl<<'\t';
	mycout<<"mycin>>count_dfa;"<<endl<<'\t';
	mycout<<"for(i=0;i<count_dfa;i++)"<<endl<<'\t'<<"{"<<endl<<"\t\t";
	mycout<<"for(j=0;j<"<<alphabet<<";j++)"<<endl<<"\t\t"<<"{"<<endl<<"\t\t\t";
	mycout<<"mycin>>dfa_array[i][j];"<<endl<<"\t\t"<<"}"<<endl<<"\t";
	mycout<<"}"<<endl<<"\t";
	mycout<<"mycin>>dfa_from;"<<endl<<'\t';
	mycout<<"for(i=0;i<count_dfa;i++)"<<endl<<"\t"<<"{"<<endl<<"\t\t";
	mycout<<"mycin>>dfa_to[i];"<<endl<<"\t"<<"}"<<endl<<"}"<<endl;
	mycout<<"int dfa_state(char *ch,int x,int y)//输出-1表示未识别 ,[x,y)左闭右开 "<<endl<<"{"<<endl;
	mycout<<"\t"<<"int now=x;"<<endl<<"\t";
	mycout<<"state=dfa_from;"<<endl<<"\t";
	mycout<<"while(!dfa_result.empty())"<<endl<<"\t"<<"{"<<endl<<"\t\t";
	mycout<<"dfa_result.pop();"<<endl<<"\t"<<"}"<<endl;
	mycout<<"while(now<y)"<<endl<<"\t"<<"{"<<endl<<"\t\t";
	mycout<<"if(dfa_to[state]!=-1)"<<endl<<"\t\t"<<"{"<<endl<<"\t\t\t";
	mycout<<"dfa_result_node temp;"<<endl<<"\t\t\t";
	mycout<<"temp.result=dfa_to[state];"<<endl<<"\t\t\t";
	mycout<<"dfa_result.push(temp);"<<endl<<"\t\t"<<"}"<<endl<<"\t\t";
	mycout<<"if(dfa_array[state][ch[now]]==-1)"<<endl<<"\t\t"<<"{"<<endl<<"\t\t\t";
	mycout<<"return -1;"<<endl<<"\t\t"<<"}"<<endl<<"\t\t";
	mycout<<"state=dfa_array[state][ch[now]];"<<endl<<"\t\t";
	mycout<<"now++;"<<endl<<"\t"<<"}"<<endl<<"\t";
	mycout<<"if(dfa_to[state]!=-1)"<<endl<<"\t"<<"{"<<endl<<"\t\t";
	mycout<<"dfa_result_node temp;"<<endl<<"\t\t";
	mycout<<"temp.result=dfa_to[state];"<<endl<<"\t\t";
	mycout<<"temp.indicator=now;"<<endl<<"\t\t";
	mycout<<"dfa_result.push(temp);"<<endl<<"\t\t";
	mycout<<"return dfa_to[state];"<<endl<<"\t"<<"}"<<endl<<"\t";
	mycout<<"return -1;"<<endl<<"}"<<endl;
	mycout<<"int dfa_state(char *ch,int x)"<<endl<<"{"<<endl<<"\t";	
	mycout<<"int len=strlen(ch);"<<endl<<"\t";
	mycout<<"return dfa_state(ch,x,x+len);"<<endl<<"}"<<endl;
	mycout<<"int main()"<<endl<<"{"<<endl<<"\t";
	mycout<<"dfa_init();"<<endl<<"}";
} 
