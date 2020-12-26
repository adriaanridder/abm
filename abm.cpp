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
 * 26 December 2020
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

/************************ sequences ***********************/
/* a sequence (k_1,...,k_n) of integers k_i in {0,1,...,n} 
 * such that sum_i (i*k_i) = n
 * Goal: generate all these sequences for a given n
 *       and store in a matrix (rows are the sequences)
 *
 * Method: it is equivalent to find all partitions of n.
 * For instance, the 7 partitions of n=5 are
 * {5}, {4,1}, {3,2}, {3,1,1}, {2,2,1}, {2,1,1,1}, {1,1,1,1,1}
 * which gives the 7x5 matrix of sequences
 * [ [0,0,0,0,1]
     [1,0,0,1,0]
     [0,1,1,0,0]
     [2,0,1,0,0]
     [1,2,0,0,0]
     [3,1,0,0,0]
     [5,0,0,0,0] ]
 * The partitions are generated lexicographically in decreasing order.
 * Start with {n}. 
 * Given a partition as an array p, say in case of n=20 the partition
 * p={7,4,3,3,1,1,1}; store the number of 1's as remaining value r. 
 * Find the rightmost p[k]>1, here p[3]=3.
 * Subtract 1 from p[k], and add 1 to r.
 * Match the remaining to the new smallest p[]>1.
 * Here, the next partition starts with {7,4,3,2} with r=4 which results
 * p = {7,4,3,2,2,2}.
 *
 * The first function counts the number of partitions of the
 * integers n = 1,2,...,N
 * Method: recursion formula. Denote c_k(n) = number of partitions
 * of integer n into k parts. Then
 * c_k(n) = c_{k-1}(n-1) + c_k(n-k).
 * Which gives c_n = sum_k c_k(n)
 */
void numsequences(int N, int C[])
{
    int j,k;
    int CC[N+1][N+1];
    for (j=0; j<=N; j++) {
        for (k=0; k<=N; k++)
            CC[j][k] = 0;
    }
    CC[0][0] = 1;
    for (j=1; j<=N; j++) {
        for (k=1; k<=j; k++) {
            CC[k][j] = CC[k-1][j-1];
            if (j-k>=1) 
                CC[k][j] += CC[k][j-k];
        }
    }
    C[0] = 0;
    for (j=1; j<=N; j++) {
        C[j] = 0;
        for (k=1; k<=j; k++)
            C[j] += CC[k][j];
    }
}

/* All sequences of length n stored in matrix B.
 * Matrix B is initialized with the right dimensions.
 * Sequences are generated as partitions, see above.
 */
void generatesequences(int n, int **B) 
{ 
    int i,k,t,r;
    int p[n]; // partition of n
    k = 0; // rightmost non-zero entry of p
    p[k] = n; // start with {n}
    t = 0; // row number of matrix B
  
    while (true) {
        for (i=0; i<k+1; i++)
            B[t][p[i]-1]++; // from partition to sequence
        t++;
  
        r = 0; // remaining value
        while ((k>=0) && (p[k]==1)) { 
            r += p[k]; 
            k--; 
        } 
  
        if (k<0)  // stop, all partition are found
            return; 
  
        p[k]--; 
        r++; 

        while (r>p[k]) {
            p[k+1] = p[k]; 
            r -= p[k]; 
            k++; 
        } 
  
        p[k+1] = r; 
        k++; 
    } 
} 

/* test function with print statements */
void printsequences(int n) 
{ 
    int i,k,r;
    int p[n];
    int q[n];
    k = 0; 
    p[k] = n; 
  
    while (true) {
        for (i=0; i<n; i++)
            q[i] = 0;
        for (i=0; i<k+1; i++)
            q[p[i]-1]++;
        for (i=0; i<n; i++)
            cout << "q[i] ";
        cout << endl;
  
        r = 0; 
        while ((k>=0) && (p[k]==1)) { 
            r += p[k]; 
            k--; 
        } 
  
        if (k<0)  
            return; 
  
        p[k]--; 
        r++; 

        while (r>p[k]) { 
            p[k+1] = p[k]; 
            r -= p[k]; 
            k++; 
        } 
  
        p[k+1] = r; 
        k++; 
    } 
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
void Hderivatives(int n, double p, int r, double H[])
{
    int i,j;
    double s;
    double A[n][r+1];

    for (j=0; j<n; j++) {
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
}

/* This function computes mu_n^* for n>=2 as
 * (1/n) sum_{sequences (k_1,...,k_{n-1})} 
 *      prod_{j=1}^{n-1} ((H_n^{(j)}(0) / j!)/k_j)^{k_j}
 * array C contains the number of sequences 
 */
double kernel(int n, double p, int r, int C[])
{
    int **K;
    int i,numseq,v,j,t;
    double mu,X;
    double H[n];

    if (n<2)
        return 1.0;

    numseq = C[n-1];
    K = new int* [numseq];
    for (i=0; i<numseq; i++)
        K[i] = new int [n-1];
    generatesequences(n-1,K);

    for (i=0; i<n; i++)
        H[i] = 0.0;
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
    int C[N+1];

    numsequences(N,C);
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
       mu = kernel(i,p,r,C);
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
        cout << "usage: goabm <m> <p> <r> <N>\n";
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
