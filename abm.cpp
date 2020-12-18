/***********************************************************/
/* ABM family for r>=2
 * Details of this family of distributions can be found in
 * 1. Bar-Lev, S.K., and A. Ridder (2020). 
 * New exponential dispersion models for count data - 
 * properties and  applications. 
 * arXiv:2003.13849v1 [math.ST] 30 Mar 2020.
 * 
 * 2. Bar-Lev, S.K. and Ridder, A. (2020).
 * Exponential dispersion models for overdispersed zero-inflated 
 * count data.
 * arXiv: 2003.13854v1 [stat.ME] 30 Mar 2020.
 * 
 * In this file the probability distribution is computed
 * when the parameters m,p,r of the variance function
 * are given. The variance function is
 * V_p(m) = m * (1 + m/p)^r, m>0, p>0, r=2,3,...
 *
 * 18 December 2020
 * Ad Ridder
 *
 */
/***********************************************************/

 
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <iostream>
#include <stack>

using namespace std; 

/************************ tree search ***********************/
/* a sequence (x_1,...,x_n) of integers x_i in {0,1,...,n} 
 * goal: all sequences such that sum_i (i*x_i) = n
 * 
 * method: construct a tree with branches of length n
 * traverse tree by depth-first search using backtracking
 *  
 * <element> is datastructure for a sequence with information
 *   length: length of the sequence (=n)
 *   path: the x_i's of the sequence
 *   sum:  sum_i (i*x_i)
 *   level: index for branching when backtracking
 *
 * Note that path[i] = x_{i+1}, i=0,...,n-1
 *
 * Elements are placed in a stack. The search continues as long as
 * the stack is non-empty.
 */
class element {
    public: 
    int length;
    int level;
    int sum;
    int *path;

    element();
    element(int);
    element(int,int);
    element(element,int);
    void printelement();
};

/* constructor of a length 1 empty element */
element::element(void)
{
    length = 1;
    level = 0;
    sum = 0;
    path = new int[1];
    path[0] = 0;
}


/* constructor of a length n empty element */
element::element(int n)
{
    int i;
    length = n;
    level = 0;
    sum = 0;
    path = new int[n];
    for (i=0; i<n; i++)
        path[i] = 0;
}

/* constructor of a length n element with path
 * x=(j,0,...,0) and level = 1
 */
element::element(int n, int j)
{
    int i;
    length = n;
    level = 1;
    sum = j;
    path = new int[n];
    path[0] = j;
    for (i=1; i<n; i++)
        path[i] = 0;
}


/* constructor of a length n element 
 * by copying an existing element with level = k,    
 * replacing x_k = j
 * updating the sum
 * and updating level = k+1
 */
element::element(element e, int j)
{
    int i,k,n;
    n = e.length;
    length = n;
    k = e.level;
    level = k + 1;
    sum = e.sum + (k+1) * (j - e.path[k]);
    path = new int[n];
    for (i=0; i<n; i++)
        path[i] = e.path[i];
    path[k] = j;
}

void element::printelement(void)
{
    int i;
    cout << "path: ";
    for (i=0; i<length; i++)
        cout << path[i] << " ";
    cout << "sum = " << sum << "  level = " << level <<"\n";
}

void printstack(stack<element> st)
{
    element e;
    printf("\nstack from top to bottom:\n");
    while (!st.empty()) {
        e = st.top();
        e.printelement();
        st.pop();  
    }
}

/* counts how many sequences (x_1,...,x_n)
 * such that n = 1*x_1 + 2*x_2 + ... + n*x_n
 */
int numsequences(int n)
{
    int j,k,s,**p;
    p = new int* [n+1];
    for (k=0; k<=n; k++) {
        p[k] = new int [n+1];
        p[k][0] = 0;
    }
    p[0][0] = 1;
    for (j=1; j<=n; j++)
        p[0][j] = 0;

    for (j=1; j<=n; j++) {
        for (k=1; k<=n; k++) {
            p[k][j] = p[k-1][j-1];
            if (j-k>=1) 
                p[k][j] += p[k][j-k];
        }
    }
    s = 0;
    for (k=1; k<=n; k++)
        s += p[k][n];

    for (k=0; k<=n; k++)
        delete [] p[k];
    delete [] p;
    return s;
}

/* This is the DFS with backtracking of the stack
 * of elements. All successfully found sequences
 * are place in a matrix B
 */
void treesearch(int n, int **B) 
{ 
    int i,j,k,s,t;
    element e;

    stack<element> mystack;
    for (j=0; j<=n; j++) { 
        e = element(n,j);
        mystack.push(e);
    }
    t = 0;
    while (!mystack.empty()) {
        e = mystack.top();
        mystack.pop();  
        i = e.level;
        s = e.sum;
        if (s==n) {
            for (j=0; j<n; j++)
                B[t][j] = e.path[j];
            t++;
        }
        else {
            if (i<n) {
                if (s+i+1 <= n) {
                    k = (int)n/(i+1);
                    for (j=0; j<=k; j++) {
                        if (s+(i+1)*j<=n)
                            mystack.push(element(e,j));
                    }
                }
            }
        }
    }
} 

/* test function with print statements */
void treesearchprint(int n) 
{ 
    int i,j,k,s,t;
    element e;

    stack<element> mystack;
    for (j=0; j<=n; j++) { 
        e = element(n,j);
        mystack.push(e);
    }
    printstack(mystack);
    t = 0;
    while (!mystack.empty()) {
        e = mystack.top();
        mystack.pop();  
        i = e.level;
        s = e.sum;
        if (s==n) {
            printf("    successfull path: ");
            e.printelement();
        }
        else {
            if (i<n) {
                if (s+i+1 <= n) {
                    k = (int)n/(i+1);
                    for (j=0; j<=k; j++) {
                        if (s+(i+1)*j<=n)
                            mystack.push(element(e,j));
                    }
                }
            }
        }
        printstack(mystack);
    }
} 

/* prints all success sequences */
void printsequences(int n)
{
    int **K;
    int numseq,i,j;

    numseq = numsequences(n);
    K = new int* [numseq];
    for (i=0; i<numseq; i++)
        K[i] = new int [n-1];
    treesearch(n,K);

    for (i=0; i<numseq; i++) {
        for (j=0; j<n; j++) 
            printf("%d ", K[i][j]);
        printf("\n");
     }
     for (i=0; i<numseq; i++)
         delete [] K[i];
     delete [] K;
}          

/********************* auxiliary *****************/
/* x^n */
double intpow(double x, int n)
{
    int i;
    double y;

    y = 1.0;
    for (i=0; i<n; i++)
        y *= x;
    return y;
}


/********************* ABM psi primitives *********/

/* primitive of 1/V(m) - 1/m  with zero integration constant
 */
double ksitilde(double m, int r)
{
    int j;
    double f,mj,y;

    f = 1.0 / (m+1.0);
    y = log(f);
    mj = f;
    for (j=1; j<r; j++) {
        y += mj / j;
        mj *= f;
    }
    return y;
}

/* primitive of 1/V_p(m) - 1/m  with zero integration constant
 */
double ksiptilde(double m, double p, int r)
{
    return ksitilde(m/p,r) - log(p);
}


/* primitive of 1/V(m)  with integration constant satisfying
 * G(0) = 1
 */
double psi(double m, int r)
{
    return ksitilde(m,r) + log(m) - ksitilde(0.0,r);
}

/* primitive of 1/V_p(m)  with integration constant satisfying
 * G_p(0) = p
 */
double psip(double m, double p, int r)
{
    return ksiptilde(m,p,r) + log(m) - ksitilde(0.0,r);
}

/* integration constant of psi
 */
double intconstpsi(int r) 
{
    return -ksitilde(0.0,r);
}

/* integration constant of psi_p
 */
double intconstpsip(double p, int r) 
{
    return -ksiptilde(0.0,p,r) - log(p);
}

/********************* ABM phi primitives *********/

/* primitive of m/V(m)  with zero integration constant
 */
double phitilde(double m, int r)
{
    double f = 1.0 / (m+1.0);
    int r1 = r-1;
    return -intpow(f,r1) / r1;
}

/* primitive of m/V_p(m)  with zero integration constant
 */
double phiptilde(double m, double p, int r)
{
    return p * phitilde(m/p,r);
}


/* primitive of m/V(m)  with integration constant satisfying
 * phi(0) = 0
 */
double phi(double m,int r)
{
    return phitilde(m,r) - phitilde(0.0,r);
}

/* primitive of m/V_p(m)  with integration constant satisfying
 * phi_p(0) = 0
 */
double phip(double m, double p, int r)
{
    return phiptilde(m,p,r) - phiptilde(0.0,p,r);
}

/* integration constant of phi
 */
double intconstphi(int r)
{
    return -phitilde(0.0,r);
}

/* integration constant of phi_p
 */
double intconstphip(double p, int r)
{
    return -phiptilde(0.0,p,r);
}

/******************** measure mu *******************/

/* this function computes
 * H_n^{(j)}(0) / j! = sum_{i=1}^{r} q_i h_n(i,j) for j=1,...,n-1 
 * 
 * The absolute value of the term q_i h_n(i,j) 
 * is stored as matrix element A_{ji}
 * Then H_n^{(j)}(0) / j! are the row sums.
 * For even j, all q_i h_n(i,j) are negative.
 */
void Hderivatives(int n, double p, int r, double *H)
{
    int i,j;
    double s,**A;

    A = new double* [n];
    for (j=0; j<n; j++) {
        A[j] = new double [r+1];
        for (i=0; i<r+1; i++)
            A[j][i] = 0.0;
    }
    for (i=1; i<r-1; i++) {
        A[1][i] = n / p;
        A[1][r-1] = (n+p) / p;
        A[1][r] = (n-r) / p;
    }

    for (j=2; j<n; j++) {
        for (i=1; i<r; i++)  
            A[j][i] = A[j-1][i] * (i+j-1) / (j*p);
        A[j][r] = A[j-1][r] / p * (1.0 - (1.0/j));
    }

    for (j=0; j<n; j++) {
        s = 0.0;
        for (i=1; i<r+1; i++)
            s += A[j][i];
        H[j] = s;
    }

    for (j=2; j<n; j+=2)
        H[j] *= -1.0;

    for (j=0; j<n; j++)
        delete [] A[j];
    delete [] A;
}

/* This function computes mu_n^* for n>=2 as
 * (1/n) sum_{sequences (k_1,...,k_{n-1})} 
 *      prod_{j=1}^{n-1} ((H_n^{(j)}(0) / j!)/k_j)^{k_j} 
 */
double kernel(int n, double p, int r)
{
    int **K;
    int i,numseq,v,j,t;
    double mu,X,*H;

    if (n<2)
        return 1.0;

    numseq = numsequences(n-1);
    K = new int* [numseq];
    for (i=0; i<numseq; i++)
        K[i] = new int [n-1];
    treesearch(n-1,K);

    H = new double [n];
    Hderivatives(n,p,r,H);
    mu = 0.0;
    for (v=0; v<numseq; v++) {
        X = 1.0; 
        for (j=1; j<n; j++) {
            X *= p;
            if (K[v][j-1] > 0) {
                for (t=0; t<K[v][j-1]; t++)
                    X *= H[j] / (t+1.0);
            }
        }  
        mu += X;
    }

    mu *= p/n;
    delete [] H;
    return mu;
}

/*********************** probabilities ************/

/* The NEF probabilities for the canonical parameterization are
 * P(X=n) = mu_n * exp(n*theta - kappa(theta)),
 * where kappa(theta) is the cumulant.
 * By the mean parameterization we have
 * theta = psi_p(m) and kappa(theta) = phi_p(m).
 *
 * This function computes these probabilities for n=0,...,N.
 */
void distribution(double m, double p, int r, int N)
{
    int i;
    double theta,kappa,mu,pr,sumpr;

    theta = psip(m,p,r);
    kappa = phip(m,p,r);

    sumpr = 0.0;
    i = 0;
    pr = exp(-kappa);
    sumpr += pr;
    printf("%3d  %.10lf\n", i,pr); 
    i = 1;
    pr = p * exp(theta-kappa);
    sumpr += pr;
    printf("%3d  %.10lf\n", i,pr); 
    for (i=2; i<N+1; i++) {
       mu = kernel(i,p,r);
       pr = mu * exp(i*theta - kappa);
       sumpr += pr;
       printf("%3d  %.10lf\n", i,pr); 
    }
    printf("\nsum = %.10lf\n", sumpr);
}

/******************** main ********************/
int main(int argc, char *argv[])
{
    int r,N;
    double m,p;

    if (argc != 5) {
        cout << "usage: go <m> <p> <r> <N>\n";
        cout << "\n";
        cout << "    m = mean\n";
        cout << "    p = dispersion parameter\n";
        cout << "    r = power\n";
        cout << "    N = length distribution\n";
        cout << "\n";
        return 0;
    }
    m = atof(argv[1]);
    p = atof(argv[2]);
    r = atoi(argv[3]);
    N = atoi(argv[4]);

    distribution(m,p,r,N);
    return 0; 
} 

/****************** EOF ***************************/
