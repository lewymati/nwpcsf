#include <bits/stdc++.h>
#define dbg(v) cerr << #v << " = " << (v) << endl;
using namespace std;

const double INF = 1000000000.0;
//const int INF = 1000000010;

namespace MaxFlowBlackBox {
    // usage: init(n, s, t), addEdge(u, v, capa u->v, capa v->u), dinicFlow()
    const int N = 100000 + 7, M = 100000 + 7;
    typedef double T; // if changing this to long long, also change INF to 10^18
    int nodes, src, dest, nedge;
    int point[M], nxt[M];
    T flow[M], capa[M];
    int head[N], dist[N], Q[N], work[N];
    void init (int _nodes, int _src, int _dest) {
    nodes = _nodes + 2; // just to be safe
    src = _src;
    dest = _dest;
    for(int i=0;i<nodes;++i)
        head[i] = -1;
    nedge = 0;
    } void addEdge(int u, int v, T c1, T c2 =
        0.0) {
        point[nedge]=v, capa[nedge]=c1, flow[nedge]=0, nxt[nedge]=head[u],
        head[u]=(nedge++);
        point[nedge]=u, capa[nedge]=c2, flow[nedge]=0, nxt[nedge]=head[v],
        head[v]=(nedge++);
    }
    bool dinicBfs() {
        for(int i=0;i<nodes;++i) dist[i] = -1;
        dist[src] = 0;
        int szQ = 1;
        Q[0] = src;
        for(int cl=0;cl<szQ;++cl) {
            for (int k = Q[cl], i = head[k]; i >= 0; i = nxt[i]) {
                if (flow[i] < capa[i] && dist[point[i]] < 0) {
                    dist[point[i]] = dist[k] + 1;
                    Q[szQ++] = point[i];
                }
            }
        }
        return dist[dest] >= 0;
    }
    T dinicDfs (int x, T exp) {
        if (x == dest) return exp;
        T res = 0;
        for (int& i = work[x]; i >= 0; i = nxt[i]) {
            int v = point[i]; T tmp;
            if (flow[i] < capa[i] && dist[x]+1 == dist[v]
                && (tmp = dinicDfs(v, min(exp, (T)capa[i] - flow[i]))) > 0) {
                flow[i] += tmp;
                flow[i^1] -= tmp;
                res += tmp;
                exp -= tmp;
                if (0 == exp) break;
            }
        }
        return res;
    }
    T dinicFlow () {
        T res = 0;
        while (dinicBfs()) {
            for(int i=0;i<nodes;++i) work[i] = head[i];
            res += dinicDfs(src,INF);
        }
        return res;
    }
}


//todo later: optimize moat adjacencies


//problem variables
int n, m, kkk;
vector<vector<int> >adj;
vector<double> w;
map<pair<int, int>, double> demands;

//algorithm variables
list<pair<set<int>, double> > activeMoats;
list<int> F; // bought vertices
set<int> Fset;
vector<pair<int, double> > codemand; //codemand[i] = <j,c>
vector<bool> codemandMarked; //codemand[i] = true if marked
vector<double> reducedW;
list<pair<set<int>, double> > inactiveSets;

//function simply returns penalty for a pair of vertices (O(1))
double pi(int i, int j) {
    if (codemand[i].first != j)
        return 0;
    else
        return codemand[i].second;
}

void readInput() {
    int a, b, c;
    scanf("%d %d %d", &n, &m, &kkk);
    for (int i=0;i<n;++i) {
        double weight;
        scanf("%lf",&weight);
        w.push_back(weight);
    }
    adj.resize(n);
    codemand.resize(n, make_pair(0,0));
    codemandMarked.resize(n, false);

    for (int i=0;i<m;++i) {
        scanf("%d %d", &a, &b);
        adj[a].push_back(b);
        adj[b].push_back(a);
    }
    for (int i=0;i<kkk;++i) {
        double penalty;
        scanf("%d %d %lf", &a, &b, &penalty);
        if (penalty <= 0.0) {
            cerr << "wrong data (demand must have positive penalty)" << endl;
            exit;
        }

        if (w[a] > 0.0 || codemand[a].second > 0.0) {
            w.push_back(0);
            vector<int> plusAdj;
            plusAdj.push_back(a);
            adj[a].push_back(n);
            adj.push_back(plusAdj);
            codemand.push_back(make_pair(0,0));
            codemandMarked.push_back(false);
            a = n;
            n += 1;
            cerr << "added vertex to get a rid of assumptions" << endl;
        }

        if (w[b] > 0.0 || codemand[b].second > 0.0) {
            w.push_back(0);
            vector<int> plusAdj;
            plusAdj.push_back(b);
            adj[b].push_back(n);
            adj.push_back(plusAdj);
            codemand.push_back(make_pair(0,0));
            codemandMarked.push_back(false);
            b = n;
            n += 1;
            cerr << "added vertex to get a rid of assumptions" << endl;
        }


        if (a>b)
            swap(a,b);

        codemand[a] = make_pair(b,penalty);
        codemand[b] = make_pair(a,penalty);
        demands[make_pair(a,b)] = penalty;
    }
}

bool moatSeparates(set<int> *moat) {
    bool result = false;
    set<int>::iterator it;
    for (it = moat->begin(); it!=moat->end(); ++it) {
        //if a moat separates an unmarked demand
        if (codemand[*it].second > 0 && !codemandMarked[*it] && moat->find(codemand[*it].first) == moat->end()) {
            result = true;
            break;
        }
    }
    return result;
}

void pruneNotActive() {
    list<pair<set<int>, double> >::iterator it;
    for (it=activeMoats.begin();it!=activeMoats.end();) {
        if (!moatSeparates(&(it->first))) {
            inactiveSets.push_back(*it);
            it = activeMoats.erase(it);
        } else {
            it++;
        }
    }
}

//n log n
void initialize() {
    //buy 0-weight vertices
    for (int i=0;i<n;++i) {
        if (w[i] == 0) {
            F.push_back(i);
            Fset.insert(i);
        }
        reducedW.push_back(w[i]);
    }

    //find activeMoats by dfs
    vector<bool> visited;
    for (int i=0;i<n;++i) {
        visited.push_back(false);
    }
    stack<int> s;
    for (list<int>::iterator it = F.begin(); it!=F.end(); ++it) {
        if (visited[*it])
            continue;
        set<int> newMoat;
        newMoat.insert(*it);
        activeMoats.push_back(make_pair(newMoat, 0.0));
        s.push(*it);
        while (!s.empty()) {
            int v = s.top();
            s.pop();
            for (vector<int>::iterator it=adj[v].begin(); it!= adj[v].end(); ++it) {
                int v2 = *it;
                if (visited[v2] || Fset.find(v2) == Fset.end())
                    continue;
                s.push(v2);
                activeMoats.back().first.insert(v2);
                visited[v2] = true;
            }
        }
    }
    pruneNotActive();
}

pair<double,int> findE1() {
    //for each vertex compute count of adjacent moats
    vector<int> adjMoatsCount;
    adjMoatsCount.resize(n,0);
    list<pair<set<int>, double> >::iterator itMoat;
    set<int> visited;
    for (itMoat=activeMoats.begin();itMoat!=activeMoats.end();++itMoat) {
        visited.clear();
        for (set<int>::iterator itV = itMoat->first.begin(); itV != itMoat->first.end();++itV) {
            for (vector<int>::iterator itAdj = adj[*itV].begin(); itAdj != adj[*itV].end(); ++itAdj) {
                if (itMoat->first.find(*itAdj)==itMoat->first.end() && visited.find(*itAdj) == visited.end()) {
                    visited.insert(*itAdj);
                    adjMoatsCount[*itAdj]++;
                }
            }
        }
    }

    //find vertex with minimum eps (reducedW/adjMoatsCount)
    double mine = INF;
    int minv = -1;
    for (int i=0;i<n;++i) {
        if (adjMoatsCount[i] > 0) {
            double eps = reducedW[i]/adjMoatsCount[i];
            if (eps < mine) {
                mine = eps;
                minv = i;
            }
        }
    }
    return make_pair(mine,minv);
}

pair<double, int> testEqualFlow(double e) {
    //left side
    int k = activeMoats.size();
    int l = inactiveSets.size();

    //right side
    int r=0;
    map<int,int> rvertex;
    for (int i=0;i<n;++i) {
        if (codemand[i].second > 0 && codemand[i].first > i) {
            rvertex[i] = 2+k+l+r;
            rvertex[codemand[i].first] = 2+k+l+r;
            r++;
        }
    }
    MaxFlowBlackBox::init(2+k+l+r,0,1);

    //add s->L edges
    list<pair<set<int>, double> >::iterator it;
    it = activeMoats.begin();
    for (int i=2;i<2+k;++i) {
        MaxFlowBlackBox::addEdge(0,i,it->second + e);
        it++;
    }
    it = inactiveSets.begin();
    for (int i=2+k;i<2+k+l;++i) {
        MaxFlowBlackBox::addEdge(0,i,it->second);
        it++;
    }

    //add L->R edges
    it = activeMoats.begin();
    for (int i=2;i<2+k;++i) {
        set<int>::iterator setit;
        for (setit = it->first.begin(); setit!=it->first.end(); ++setit) {
            //if a moat separates an unmarked demand
            if (codemand[*setit].second > 0 && it->first.find(codemand[*setit].first) == it->first.end()) {
                MaxFlowBlackBox::addEdge(i,rvertex[*setit],INF);
            }
        }
        it++;
    }

    it = inactiveSets.begin();
    for (int i=2+k;i<2+k+l;++i) {
        set<int>::iterator setit;
        for (setit = it->first.begin(); setit!=it->first.end(); ++setit) {
            //if a moat separates an unmarked demand
            if (codemand[*setit].second > 0 && it->first.find(codemand[*setit].first) == it->first.end()) {
                MaxFlowBlackBox::addEdge(i,rvertex[*setit],INF);
            }
        }
        it++;
    }

    //add R->t edges
    int ir = 0;
    for (int i=0;i<n;++i) {
        if (codemand[i].second > 0 && codemand[i].first > i) {
            MaxFlowBlackBox::addEdge(2+k+l+ir, 1, codemand[i].second);
            ir++;
        }
    }
    double cost = MaxFlowBlackBox::dinicFlow();

    int kk = 0;
    for (int i=2;i<2+k;++i) {
        if (MaxFlowBlackBox::dist[i] == -1)
            kk++;
    }
    return make_pair(cost, kk);
}

double findE2() {
    int k = activeMoats.size();
    if (k==0)
        return INF;
    double e = 0;
    //take initial e=(sum pij - sum ys)/k
    for (int i=0;i<n;++i) {
        if (codemand[i].second > 0 && codemand[i].first > i) {
            e += codemand[i].second;
        }
    }
    double sumys = 0;
    list<pair<set<int>, double> >::iterator it;
    for (it = activeMoats.begin();it != activeMoats.end();++it) {
        sumys += it->second;
    }
    for (it = inactiveSets.begin();it != inactiveSets.end();++it) {
        sumys += it->second;
    }
    e = (e-sumys)/k;

    pair<double, int> res = testEqualFlow(e);
    double cost = res.first;
    double kk = res.second;
    while (cost + 0.0000001 < sumys+k*e) {
        double D = sumys+k*e - cost;
        e -= D/(k-kk);
        pair<double, int> res = testEqualFlow(e);
        cost = res.first;
        kk = res.second;
        if (e<0.0000001) {
            e = 0;
            break;
        }
    }
    testEqualFlow(e+0.000000001);
    return e;
}

void increaseActiveMoats(double e) {
    list<pair<set<int>, double> >::iterator it;
    for (it = activeMoats.begin();it != activeMoats.end();++it) {
        it->second += e;
    }

    //update residual weights

    //for each vertex compute count of adjacent moats
    vector<int> adjMoatsCount;
    adjMoatsCount.resize(n,0);
    list<pair<set<int>, double> >::iterator itMoat;
    set<int> visited;
    for (itMoat=activeMoats.begin();itMoat!=activeMoats.end();++itMoat) {
        visited.clear();
        for (set<int>::iterator itV = itMoat->first.begin(); itV != itMoat->first.end();++itV) {
            for (vector<int>::iterator itAdj = adj[*itV].begin(); itAdj != adj[*itV].end(); ++itAdj) {
                if (itMoat->first.find(*itAdj)==itMoat->first.end() && visited.find(*itAdj) == visited.end()) {
                    visited.insert(*itAdj);
                    adjMoatsCount[*itAdj]++;
                }
            }
        }
    }

    //update residuals
    for (int i=0;i<n;++i) {
        if (adjMoatsCount[i] > 0) {
            reducedW[i] -= e*adjMoatsCount[i];
        }
    }  
}

void mergeMoatsAroundV(int v) {
    pair<set<int>,double> newMoat;
    newMoat.first.insert(v);
    newMoat.second = 0.0;
    list<pair<set<int>, double> >::iterator itMoat;
    for (itMoat=activeMoats.begin();itMoat!=activeMoats.end();) {
        bool breakk = false;
        for (set<int>::iterator itV = itMoat->first.begin(); itV != itMoat->first.end();++itV) {
            for (vector<int>::iterator itAdj = adj[*itV].begin(); itAdj != adj[*itV].end(); ++itAdj) {
                if (*itAdj == v) {
                    inactiveSets.push_back(*itMoat); //TODO if second>0?
                    newMoat.first.insert(itMoat->first.begin(), itMoat->first.end());
                    itMoat = activeMoats.erase(itMoat);
                    breakk = true;
                    break;
                }
            }
            if (breakk)
                break;
        }
        if (!breakk)
            ++itMoat;
    }

    for (itMoat=inactiveSets.begin();itMoat!=inactiveSets.end();++itMoat) {
        bool breakk = false;
        for (set<int>::iterator itV = itMoat->first.begin(); itV != itMoat->first.end();++itV) {
            for (vector<int>::iterator itAdj = adj[*itV].begin(); itAdj != adj[*itV].end(); ++itAdj) {
                if (*itAdj == v) {
                    newMoat.first.insert(itMoat->first.begin(), itMoat->first.end());
                    breakk = true;
                    break;
                }
            }
            if (breakk)
                break;
        }
    }
    activeMoats.push_back(newMoat);
}

void freezeFamily() {
    list<pair<set<int>, double> >::iterator it;
    int k = activeMoats.size();
    it = activeMoats.begin();
    for (int i=2;i<2+k;++i) {
        if (MaxFlowBlackBox::dist[i] > -1) {
            for (set<int>::iterator itV = it->first.begin(); itV != it->first.end(); ++itV) {
                if (codemand[*itV].second > 0 && !codemandMarked[*itV] && it->first.find(codemand[*itV].first) == it->first.end()) {
                    codemandMarked[*itV] = true;
                }
            }
            inactiveSets.push_back(*it);
            it = activeMoats.erase(it);
        } else
            it++;
    }
}

bool testRemoval(int v) {
    Fset.erase(Fset.find(v));
    vector<int> cc;
    stack<int> ss;
    cc.resize(n,-1);
    int ccc = 0;
    for (int i=0;i<n;++i) {
        if (cc[i] == -1 && Fset.find(i) != Fset.end()) {
            ss.push(i);
            cc[i] = ccc;
            while (!ss.empty()) {
                int v = ss.top();
                ss.pop();
                for (vector<int>::iterator it = adj[v].begin(); it!= adj[v].end();++it) {
                    if (cc[*it] == -1 && Fset.find(*it) != Fset.end()) {
                        cc[*it] = ccc;
                        ss.push(*it);
                    }
                }
            }
            ccc++;
        }
    }
    Fset.insert(v);
    for (int i=0;i<n;++i) {
        if (codemand[i].second > 0 && !codemandMarked[i] && cc[i] != cc[codemand[i].first]) {
            return false;
        }
    }
    return true;
}

void prunePhase() {
    list<int>::iterator it = F.end();
    while (it != F.begin())
    {
        it--;
        if (testRemoval(*it)) {
            Fset.erase(Fset.find(*it));
            it = F.erase(it);
        }
    }
}

double getDualsSum() {
    double sumys = 0;
    list<pair<set<int>, double> >::iterator it;
    for (it = activeMoats.begin();it != activeMoats.end();++it) {
        sumys += it->second;
    }
    for (it = inactiveSets.begin();it != inactiveSets.end();++it) {
        sumys += it->second;
    }
    return sumys;
}

double getNodesCost() {
    double result = 0;
    list<int>::iterator it;
    for (it = F.begin(); it!=F.end();++it) {
        result += w[*it];
    }
    return result;
}

double getPenalty() {
    //find connected components
    vector<int> cc;
    stack<int> ss;
    cc.resize(n,-1);
    int ccc = 0;
    for (int i=0;i<n;++i) {
        if (cc[i] == -1 && Fset.find(i) != Fset.end()) {
            ss.push(i);
            cc[i] = ccc;
            while (!ss.empty()) {
                int v = ss.top();
                ss.pop();
                for (vector<int>::iterator it = adj[v].begin(); it!= adj[v].end();++it) {
                    if (cc[*it] == -1 && Fset.find(*it) != Fset.end()) {
                        cc[*it] = ccc;
                        ss.push(*it);
                    }
                }
            }
            ccc++;
        }
    }
    double result = 0.0;
    for (int i=0;i<n;++i) {
        if (codemand[i].second > 0 && (cc[i] != cc[codemand[i].first] || cc[i] == -1)) {
            result += codemand[i].second;
        }
    }
    return result/2.0;
}


int main() {
    readInput();
    initialize();
    int a = 0;
    double e1,e2;
    while (!activeMoats.empty()) {
        a++;
        pair<double,int> ev = findE1();
        e1 = ev.first;
        if (e1 > 0)
            e2 = findE2();
        dbg(e1);
        dbg(e2);
        increaseActiveMoats(min(e1,e2));
        if (e1 <= e2) {
            F.push_back(ev.second);
            Fset.insert(ev.second);
            mergeMoatsAroundV(ev.second);
            pruneNotActive();
        } else {
            freezeFamily();
        }
    }
    prunePhase();
    for (list<int>::iterator it = F.begin(); it!=F.end(); ++it){
        printf("%d ", *it);
    }
    printf("\n");
    dbg(getDualsSum());
    dbg(getNodesCost());
    dbg(getPenalty());
    return 0;
}
