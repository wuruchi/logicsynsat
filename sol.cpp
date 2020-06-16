#include <iostream>
#include <fstream>
#include <time.h>
#include <sstream>
#include <vector>
#include <algorithm>
#include <assert.h>
#include <stdlib.h>
#include <math.h>

#define V +

using namespace std;

// For heap of lentgth 1, n = 1
int n = 4;
int n_vars;
int n_clauses;
int heapSize;
int numIndicaPerNode;
int overHead;
int innerOverHead;

int numRows = 0;
int numVars = 0;

vector<int> result;

ofstream cnf;
ifstream sol;

typedef string literal;
typedef string  clause;

literal operator-(const literal& lit) {
  if (lit[0] == '-') return lit.substr(1); 
  else               return "-" + lit;
}

// static values (result, constant 0, input variables)
literal x(int i, int j) {
  // assert(0 <= i and i < n);
  // assert(0 <= j and j < n);
  assert(0 <= i);
  assert(0 <= j);
  return to_string(i*numRows + j + 1) + " ";
}

// indicators per node
literal indicator(int i, int j) {
  assert(0 <= i);
  assert(0 <= j);
  return to_string(overHead + i*(numVars + 2) + j + 1) + " ";
}

// inner values of nodes
literal inner(int i, int j) {
  assert(0 <= i);
  assert(0 <= j);
  return to_string(innerOverHead + i*numRows + j + 1) + " ";
}


void add_clause(const clause& c) {
  cnf << c << "0" << endl;
  ++n_clauses;
}

void add_amo(const vector<literal>& z) {
  int N = z.size();
  for (int i1 = 0; i1 < N; ++i1)
    for (int i2 = i1+1; i2 < N; ++i2)
      add_clause(-z[i1] V -z[i2]);
}

// vector<int> combination;
// void pretty_print(const vector<literal>& v) {
//   //static int count = 0;
//   cout << "combination " <<  ": [ ";
//   for (int i = 0; i < v.size(); ++i) { cout << v[i] << " "; }
//   cout << "] " << endl;
// }


void go(vector<literal>& combination, int offset, int k,const vector<literal>& z) {
  
  if (k == 0) {
    // for (int i = 0; i < combination.size(); ++i)
    //   cout << combination[i] << " - " << endl;
    //pretty_print(combination);
    clause c;
    for (int i = 0; i < combination.size(); ++i) { 
      c = c V -combination[i];
      //cout << combination[i] << " "; 
    }
    add_clause(c);
    return;
  }
  //cout << heapSize << " offset: " << offset << endl;
  for (int i = offset; i <= z.size() - k; ++i) {
    combination.push_back(z[i]);
    go(combination,i+1, k-1, z);
    combination.pop_back();
  }
}

//Builds at most k ( < k)
void add_amk(const vector<literal>& z, int k){
  int N = z.size();
  vector<literal> combination;
  go(combination, 0, k, z);

}

void write_CNF(int atMostNor){
  // Results * 2 (1 for results, 1 for constant 0) + number of Variables * numberRows (Truth Table) +
  // numRows * heapSize (inner indicator per each node)
  // (number of Variables (1 indicator per variable) + 2(0 constant indicator, node indicator) ) * heapSize (Treesize)
  // Overhead = (numRows * 2) + (numVars * numRows)
  numIndicaPerNode = (numVars + 2);
  n_vars = (numRows * 2) + (numVars * numRows) + (numRows * heapSize) + numIndicaPerNode * heapSize;
  //cout << "Num vars: " << n_vars << endl;
  // number of static variables
  overHead = (numRows * 2) + (numVars * numRows) + (numRows * heapSize);
  innerOverHead = (numRows * 2) + (numVars * numRows);
  // Truth table again. Avoid passing 2d matrixed or vector to function
  int vars[numVars + 1][numRows];

  // Building truth table
  for(int i = 0; i < numRows; ++i)
    vars[0][i] = 0;


  for (int j = 0; j < numRows; ++j){
    int n = j;
    for (int k = 1; k <= numVars; ++k){
      vars[numVars + 1 - k][j] = n % 2;
      //cout << n%2 <<  endl;
      n = n/2;
    }
  }

  // Set results in first column
  for (int j = 0; j < numRows; ++j){
    //body.push_back(i);
    clause c;
    if (result[j] == 0)
      c = -x(0,j);
    else
      c = x(0,j);

    add_clause(c);
  }

  // Set values for constant 0
  for (int j = 0; j < numRows; ++j){
    clause c;
    c = -x(1,j);
    add_clause(c);
  }

  // Set values of each variable
  for (int i = 0; i < numVars; ++i){
    for (int j = 0; j < numRows; ++j){
      clause c;
      if (vars[i+1][j] == 0)
        c = -x(i+2,j);
      else
        c = x(i+2, j);
      add_clause(c);
    }
  }

  // Root node is equal to results
  for(int j = 0; j < numRows; ++j){
    add_clause(-x(0,j) V inner(0,j));
    add_clause(x(0,j) V -inner(0,j));
  }

  // If an item of the heap assumes the values of the constant 0, the corresponding indicator assumes TRUE
  for(int i = 0; i < heapSize; ++i){
    for(int j = 0; j < numRows; j++){
      add_clause(-inner(i,j) V -indicator(i,0));
    }
  }

  // If an item of the heap assumes the values of a variable, the corresponding indicator assumes TRUE
  for(int k = 1; k <= numVars; ++k){
    for (int i = 0; i < heapSize; ++i){
      for(int j = 0; j < numRows; ++j){
        add_clause(-indicator(i,k) V -x(i + numVars + 2,j) V x(k + 1,j));
        add_clause(-indicator(i,k) V x(i + numVars + 2,j) V -x(k + 1,j));
      }
    }
  }


  //If an item of the heap assumes the role of Nor Gate, the result is calculated and stored in the corresponding inner
  //The corresponding indicator assumes the value TRUE
  for(int i = 0; i < heapSize; ++i){
    for(int j = 0; j < numRows; ++j){
      if ((2*i + 1) <= (heapSize - 1) || (2*i + 2) <= (heapSize - 1)){
        //cout << indicator(i, numIndicaPerNode - 1) << " : " << inner(i,j) << " < " << inner(2*i + 1, j) << " nor " << inner(2*i + 2, j)  << endl;
        
        add_clause(-indicator(i, numIndicaPerNode - 1) V inner(2*i + 1, j) V inner(2*i + 2, j) V inner(i,j) );
        add_clause(-indicator(i, numIndicaPerNode - 1) V -inner(2*i + 1, j) V -inner(i,j));
        add_clause(-indicator(i, numIndicaPerNode - 1) V -inner(2*i + 2, j) V -inner(i,j));
      }
    }
  }
    

  // conditioning indicators at most one per item of heap
  for(int i = 0; i < heapSize; ++i){
    vector<literal> z;
    for(int j = 0; j < numIndicaPerNode; ++j){
      z.push_back(indicator(i,j));
      //cout << indicator(i,j) << endl;
    }
    add_amo(z);
  }

 


  // conditioning indicators at least one per item of heap
  for(int i = 0; i < heapSize; ++i){
    //vector<literal> z;
    clause c;
    for(int j = 0; j < numIndicaPerNode; ++j){
      c = c V indicator(i,j);
      //cout << indicator(i,j) << endl;
    }
    add_clause(c);
  }

  //Leaves cannot be gates
  for(int i = 0; i < heapSize; i++){
    if((2*i + 1) > (heapSize - 1)){
      //cout << overHead << " ov : i " << i << " , indicaPerNode : " << numIndicaPerNode << endl;
      add_clause(-indicator(i,numIndicaPerNode - 1));
    }
  }

  //This is conditioned by iteration. Number of nor gates at most atMostNor
  vector<literal> z1;
  for(int i = 0; i < heapSize; ++i){
    if((2*i + 1) <= (heapSize - 1)){
      z1.push_back(indicator(i, numIndicaPerNode - 1));
    }
  }
  if (atMostNor == 0){
    for(int i = 0; i < heapSize; ++i){
      add_clause(-indicator(i, numIndicaPerNode - 1));
    }
  }else if (z1.size() == atMostNor){
    clause c;
    for(int i = 0; i < atMostNor; ++i){
      c = c V z1[i];
    }
    add_clause(c);
  }else{
    add_amk(z1,atMostNor);
  }

  cnf << "p cnf " << n_vars << " " << n_clauses << endl;


}



// Gets the solution from the result of lingeling
void get_solution(vector<int>& q) {
  int lit;
  int i = 0;
  while (sol >> lit){
    if (i >= overHead && lit != 0) {
      q.push_back(lit);
    }
    i++;
  }  
}

// Tells which is the role of the heap item based on its indicators
int whichone(vector<int>& q){
  for (int i = 0; i < q.size(); ++i){
    if (q[i] > 0){
      if (i == numIndicaPerNode - 1)
        return -1;
      return i;
    }
  }
  return 0;
}

// Calculates depth of solution
int calculateDepth(int indexHeap){
  //cout << indexHeap << endl;
  int depth = 0;
  int parent = 0;
  if (indexHeap == -1) return depth;
  if (indexHeap == 0) return 1;
  depth++;
  parent = floor((indexHeap - 1)/2);
  depth++;
  while (parent > 0){
    parent = floor((parent - 1)/2);
    depth++;
  }
  return depth;
}

//Prints body of solution
void printGraph(vector<int> codesL, int current){
  //int currentLength = sizeof(codes);
  if (codesL[current] >= 0){
    cout << current + 1 << " " << codesL[current] << " 0 0" << endl;
  }
  else if(codesL[current] == -1)
  {
    cout << current + 1 << " " << codesL[current] << " " << (2*current + 1) + 1 << " " << (2*current + 2) + 1 << endl;
    printGraph(codesL, (2*current + 1));
    printGraph(codesL, (2*current + 2));  
  }
}

// Marks a children as not relevant
void discardChildren(vector<int>& base, int i){
  int left = 2*i + 1;
  int right = 2*i + 2;
  //cout << "l: " << left << "- r:" << right << endl;
  if (left <= heapSize - 1 && right <= heapSize -1){
    //cout << "set base" << endl;
    base[left] = -2;
    base[right] = -2;
    discardChildren(base,left);
    discardChildren(base,right);
  }
}

// Walks the graph cleaning the heap
void walkBase(vector<int>& base){
  //vector<int> discarded;
  int index = 0;
  for (int i = 0; i < heapSize; ++i){
    if (base[i] != -1){
      // Subtree is discarded
      discardChildren(base,i);
    }
  }  
}

// Writes Solution
void write_solution(const vector<int>& q) {
  if (q.size() == 0) return;
  cout << numVars << endl;
  for(int i = 0; i < result.size(); ++i)
    cout << result[i] << endl;

  int range = numVars + 2;
  vector<int> baseResult;
  for(int i = 0; i < heapSize; ++i){
    vector<int> r;
    for(int j = 0; j < numVars + 2; ++j){
      r.push_back(q[i*range + j]);
    }
    baseResult.push_back(whichone(r));
  }
  int norCount = 0;
  int lastNode = -1;
  
  //int codes[heapSize];
  walkBase(baseResult);

  
  for(int i = 0; i < heapSize; ++i){
    //cout << "base i : " << i << " = " << baseResult[i] << endl;
    if (baseResult[i] == -1){
      norCount++;
      lastNode = i;
    }
  }
  
  cout << calculateDepth(lastNode) << " " << norCount << endl;

  // for(int i = 0; i < heapSize; ++i)
  //     cout << codes[i] << endl;

  printGraph(baseResult,0);
}

int main() {
  //cout << "Enter main: " << endl;
  cin >> numVars;
  numRows = pow(2,numVars);
  //cout << numRows << endl;
  //fixedLength = pow(2,numVars) - 1;
  for (int k = 0; k < numRows; ++k) {
    int now;
    cin >> now;
    result.push_back(now);
  }
  //int inc = 1;
  //heapSize = pow(2,inc) - 1;
  heapSize = 1;
  int validate = 0;

  while(validate <= 0){
    n_clauses = 0;
    int maxNor = floor(heapSize/2);
    int currentNor = 1;
    while(currentNor <= maxNor && validate <=0){
      n_clauses = 0;
      //cout << " Trying heap " << heapSize << " less than nor gates " << currentNor << endl;
      cnf.open("tmp.rev");
      write_CNF(currentNor);

      cnf.close();

      // Linux
      // system("tac tmp.rev | lingeling | grep -E -v \"^c\" | tail -l=+2 | cut --delimiter=' ' --field=1 --complement > tmp.out");

      // MacOS
      system("tac tmp.rev | lingeling | grep -E -v \"^c\" | tail -n +2 | gcut --delimiter=' ' --field=1 --complement  > tmp.out");

      vector<int> q;
      sol.open("tmp.out");
      get_solution(q);
      validate = q.size();
      sol.close();
      write_solution(q);
      currentNor++;
    }

    heapSize += 2;
  }
}