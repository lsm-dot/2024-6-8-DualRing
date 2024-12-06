/*
 *   Elliptic Curve Digital Signature Algorithm (ECDSA)
 *
 *
 *   This program generates one set of public and private keys in files
 *   public.ecs and private.ecs respectively. Notice that the public key
 *   can be much shorter in this scheme, for the same security level.
 *
 *   It is assumed that Curve parameters are to be found in file common.ecs
 *
 *   The curve is y^2=x^3+Ax+B mod p
 *
 *   The file common.ecs is presumed to exist, and to contain the domain
 *   information {p,A,B,q,x,y}, where A and B are curve parameters, (x,y) are
 *   a point of order q, p is the prime modulus, and q is the order of the
 *   point (x,y). In fact normally q is the prime number of points counted
 *   on the curve.
 *
 *   Requires: big.cpp ecn.cpp
 */

#include <iostream>
#include <fstream>
#include "ecn.h"
#include <ctime>
#include <vector>
#include <sstream>
#pragma pack(1)



using namespace std;
extern "C" {
#include "miracl.h"
#include "mirdef.h"

//#include "ec2.h"
}
// if MR_STATIC defined, it should be 20

#ifndef MR_NOFULLWIDTH
Miracl precision = 20;
#else
Miracl precision(20, MAXBASE);
#endif

struct KeyParams {
    Big q;
    //Big dk, tau;
    ECn G, ek, vk, u;
};

struct NISA
{
    Big b, a;
    vector<ECn> pi_L, pi_R;
};

struct Tag
{
    Big za, zb, zs;
    pair<ECn, ECn> A, B, d;
};

struct Open
{
    ECn pk;
    ECn A;
    ECn B;
    Big z;
};

struct basic_sigma
{
    vector<Big> c_array; 
    Big z;
    Big c_number;
    Big r1;
    ECn R;
    pair<ECn, ECn> C;  
    vector<ECn> new_pk_list;
};

struct sigma
{
    vector<Big> c_array;
    Big z;
    ECn R;
    pair<ECn, ECn> C;
    NISA pi;
    Tag tag;
};

std::pair<ECn, ECn> ElGamal_Enc(KeyParams& params, ECn& vk, ECn& pk, Big& r1) {
    ECn c1 = r1 * params.G;
    //c1 *= r1;
    //c1 *= r1;
    ECn c2 = r1 * vk;
    //c2 *= r1;
    c2 += pk;
    return {c1, c2};
}

ECn ElGamal_Dec(KeyParams& params, Big& dk, ECn& c1, ECn& c2) {
    ECn invers = -dk * c1;
    ECn m = c2;
    m += invers;
    return m;
}

void KeyGen(KeyParams& params, Big& sk, ECn& pk) {
    sk = rand(params.q);
    pk = sk * params.G;
}

// Helper method to convert a point to Big form
void ECn_to_Big(sha& sh, ECn& point) {
    Big a, x, y;
    //point.norm();
    // 用于将椭圆曲线点从同类坐标（projective coordinates）(x, y, z) 转换为仿射坐标（affine coordinates）(x, y)
    normalise(point);
    point.getxy(x, y);
    int i, m;
    //x.g.get(X, Y);
    a = x;
    while (a > 0)
    {
        m = a % 256;
        shs_process(&sh, m);
        a /= 256;
    }
    a = y;
    while (a > 0)
    {
        m = a % 256;
        shs_process(&sh, m);
        a /= 256;
    }

}

// Helper method to convert a list of public keys to a Big
void list_to_Big(sha& sh, vector<ECn>& pk_list) {
    //string result;
    for (auto pk : pk_list) {
        ECn_to_Big(sh, pk);
    }
    //return result;
}

void add_to_hash(sha& sh, const Big& x)
{
    int m;
    Big a = x;
    while (a > 0)
    {
        m = a % 256;
        shs_process(&sh, m);
        a /= 256;
    }
}

Big H1(char* string)
{ // Hash a zero-terminated string to a number < modulus
    Big h, p;
    char s[20];
    int i, j;
    sha sh;

    shs_init(&sh);

    for (i = 0;; i++)
    {
        if (string[i] == 0) break;
        shs_process(&sh, string[i]);
    }
    shs_hash(&sh, s);
    p = get_modulus();
    h = 1; j = 0; i = 1;
    forever
    {
        h *= 256;
        if (j == 20) { h += i++; j = 0; }
        else         h += s[j++];
        if (h >= p) break;
    }
    h %= p;
    return h;
}

Big finish_hash_to_group(KeyParams& params, sha& sh)
{
    Big hash;
    char s[20];
    shs_hash(&sh, s);
    hash = from_binary(20, s);
    return hash % params.q;
}

basic_sigma basic_sign(KeyParams& params, vector<ECn>& pk_list, Big& sk, int k, char* m) {
    int len = pk_list.size();
    Big r1 = rand(params.q);
    pair<ECn, ECn> C;
    
    C = ElGamal_Enc(params, params.vk, pk_list[k], r1);
    //c1 = C.first;
    ECn c2 = C.second;

    vector<Big> c_array(len);
    vector<ECn> new_pk_list(len);

    for (int i = 0; i < len; i++)
    {
        new_pk_list[i] = c2;
        new_pk_list[i] -= pk_list[i];
    }
    Big r = rand(params.q);
    ECn R = r * params.vk;
    Big summation_except_j = 0;
    for (int i = 0; i < len; i++)
    {
        if (i == k)
        {
            continue;
        }
        Big temp_c = rand(params.q);
        c_array[i] = temp_c;
        R += temp_c * new_pk_list[i];
		summation_except_j += temp_c;
    }
    //string this_string = m + list_to_string(new_pk_list) + pt_to_string(R);
    Big temp_m = H1(m);
    sha sh;
    shs_init(&sh);
    
    
    add_to_hash(sh, temp_m);
    list_to_Big(sh, new_pk_list);
    ECn_to_Big(sh, R);

    Big c_number = finish_hash_to_group(params, sh);
  
    c_array[k] = (c_number - summation_except_j) % params.q;
    Big z = r - r1 * c_array[k];

    return { c_array, z, c_number, r1, R, C, new_pk_list };
}

// 检查一个点是否是无穷远点
//bool is_infinity(ECn& point) {
//    return point.iszero();
//}
//
//// 比较两个点
//bool are_points_equal(ECn& point1, ECn& point2) {
//    return point1 == point2;
//}

bool basic_verify(KeyParams& params, char* m, vector<ECn>& pk_list, basic_sigma& bsigma) {
    //ECn vk = params.vk;
    Big z = bsigma.z;
    pair<ECn, ECn> C = bsigma.C;
    vector<Big> c_array = bsigma.c_array;
    ECn R = bsigma.R;
	int len = pk_list.size();

    ECn R1 = z * params.vk;
    Big c_sum = 0;
    ECn c2 = C.second;
    vector<ECn> new_pk_list(len);

    for (int i = 0; i < len; i++)
    {
        new_pk_list[i] = c2;
        new_pk_list[i] -= pk_list[i];
    }

    for (int i = 0; i < len; i++)
    {
        R1 += c_array[i] * new_pk_list[i];
        c_sum += c_array[i];
    }
    
    Big temp_m = H1(m);

    sha sh;

    shs_init(&sh);
    
    add_to_hash(sh, temp_m);
    list_to_Big(sh, new_pk_list);
    ECn_to_Big(sh, R1);

    Big result = finish_hash_to_group(params, sh);
    
    if ((c_sum % params.q) != result)
    {
        cout << "basic verify faliure!" << endl;
        return false;
    }
    return true;
}

NISA P_proof(KeyParams& params, vector<ECn>& new_pk_list, ECn& this_u, vector<Big>& b, vector<Big>& a, vector<ECn>& pi_L, vector<ECn>& pi_R) {
    /*vector<Big> b_prime_list;
    vector<Big> a_prime_list;*/
    int n = a.size();
    if (n == 1)
    {
        return { b[0], a[0], pi_L, pi_R };
    }

    int n_prime = int(n / 2);
    Big c_L = 0, c_R = 0;
    for (int i = 0; i < n_prime; i++)
    {
        c_R += (a[n_prime + i] * b[i]) % params.q;
        c_L += (a[i] * b[n_prime + i] % params.q);
    }
    ECn my_L, my_R;
    my_L = c_L * this_u;
    my_R = c_R * this_u;

    for (int i = 0; i < n_prime; i++)
    {
        my_L += a[i] * new_pk_list[n_prime + i];
        my_R += a[n_prime + i] * new_pk_list[i];
    }
    pi_L.push_back(my_L);
    pi_R.push_back(my_R);

    sha sh;
    shs_init(&sh);
    ECn_to_Big(sh, my_L);
    ECn_to_Big(sh, my_R);
    
    Big x = finish_hash_to_group(params, sh);

    vector<ECn> pk_prime_list(n_prime);
    vector<Big> a_prime_list(n_prime);

    Big x_inverse = inverse(x, params.q);
    Big b_value = (x_inverse * b[0] + x * b[n_prime]) % params.q;
    vector<Big> b_prime_list(n_prime, b_value);

    for (int i = 0; i < n_prime; i++)
    {
        pk_prime_list[i] = x_inverse * new_pk_list[i];
        pk_prime_list[i] += x * new_pk_list[n_prime + i];
        a_prime_list[i] = (x * a[i] + x_inverse * a[n_prime + i]) % params.q;
    }

    return P_proof(params, pk_prime_list, this_u, b_prime_list, a_prime_list, pi_L, pi_R);
}

int check_bit(int i, int j) {
    int temp = i;
    if (((temp >> j) & 1) == 1) {
        return 1;
    }
    return -1;
}

bool V(KeyParams& params, vector<ECn>& new_pk_list, ECn& this_u, ECn& P, NISA& pi) {
    int original_length = new_pk_list.size();
    int log_length = int(log2(original_length));
    vector<Big> x_list(log_length);

    Big b = pi.b;
    Big a = pi.a;
    vector<ECn> pi_L = pi.pi_L;
    vector<ECn> pi_R = pi.pi_R;

    for (int i = 0; i < log_length; i++)
    {
        sha sh;
        shs_init(&sh);
        ECn_to_Big(sh, pi_L[i]);
        ECn_to_Big(sh, pi_R[i]);

        x_list[i] = finish_hash_to_group(params, sh);
    }
    vector<Big> y_list(original_length);

    for (int i = 0; i < original_length; i++)
    {
        Big product = 1;
        for (int ii = 0; ii < log_length; ii++)
        {
            if (check_bit(i, ii) == 1)
            {
                product = (product * x_list[log_length - ii - 1]) % params.q;
            }
            else {
                Big x_inverse = inverse(x_list[log_length - ii - 1], params.q);
                product = (product * x_inverse) % params.q;
            }
        }
        y_list[i] = product;
    }
    ECn g_prime = y_list[0] * new_pk_list[0];

    for (int iv = 1; iv < original_length; iv++)
    {
        g_prime += y_list[iv] * new_pk_list[iv];
    }
    ECn left_check = P;
    for (int v = 0; v < log_length; v++)
    {
        Big x_sq = pow(x_list[v], 2, params.q);
        left_check += x_sq * pi_L[v];
        left_check += inverse(x_sq, params.q) * pi_R[v];
    }
    ECn right_check = b * this_u;
    right_check += g_prime;
    right_check *= a;

    if (left_check == right_check)
    {
        return true;
    }
    return false;
}

NISA NISA_Proof(KeyParams& params, vector<ECn>& new_pk_list, ECn& P, Big& c, vector<Big>& a){
    sha sh;

    shs_init(&sh);
    ECn_to_Big(sh, P);
    ECn_to_Big(sh, params.u);
    add_to_hash(sh, c);
    Big h = finish_hash_to_group(params, sh);
    ECn uprime = h * params.u;

    int len = new_pk_list.size();
    Big b_initial = 1;
    vector<Big> b(len, b_initial);
    vector<ECn> pi_L;
    vector<ECn> pi_R;

    return P_proof(params, new_pk_list, uprime, b, a, pi_L, pi_R);
}

bool NISA_Verify(KeyParams& params, vector<ECn>& new_pk_list, ECn& P, Big& c, NISA& pi) {
    
    sha sh;

    shs_init(&sh);
    ECn_to_Big(sh, P);
    ECn_to_Big(sh, params.u);
    add_to_hash(sh, c);
    Big h = finish_hash_to_group(params, sh);

    ECn uprime = h * params.u;
    ECn P_prime = P;
    P_prime += c * uprime;
    return V(params, new_pk_list, uprime, P_prime, pi);
}

Tag tag_proof(KeyParams& params, ECn& pk, Big& sk, Big& r, pair<ECn, ECn>& C, NISA& pi, char* m) {
    Big b = pi.b;
    Big a = pi.a;
    vector<ECn> pi_L = pi.pi_L;
    vector<ECn> pi_R = pi.pi_R;
    ECn c1 = C.first;
    ECn c2 = C.second;

    Big s = rand(params.q);
    Big t = rand(params.q);
    Big ar = rand(params.q);
    Big br = rand(params.q);

    ECn Gs = s * params.G;
    pair<ECn, ECn> d = ElGamal_Enc(params, params.ek, pk, t);
    pair<ECn, ECn> A = ElGamal_Enc(params, params.vk, Gs, ar);
    pair<ECn, ECn> B = ElGamal_Enc(params, params.ek, Gs, br);

    Big temp_m = H1(m);
    sha sh;
    shs_init(&sh);

    add_to_hash(sh, temp_m);
    add_to_hash(sh, b);
    add_to_hash(sh, a);
    list_to_Big(sh, pi_L);
    list_to_Big(sh, pi_R);
    ECn_to_Big(sh, c1);
    ECn_to_Big(sh, c2);

    Big c = finish_hash_to_group(params, sh);
    Big zs = sk * c + s;
    Big za = r * c + ar;
    Big zb = t * c + br;

    return { za, zb, zs, A, B, d };
}

bool tag_verify(KeyParams& params, pair<ECn, ECn>& C, NISA& pi, char* m, Tag& tag) {
    Big b = pi.b;
    Big a = pi.a;
    vector<ECn> pi_L = pi.pi_L;
    vector<ECn> pi_R = pi.pi_R;
    ECn c1 = C.first;
    ECn c2 = C.second;

    Big temp_m = H1(m);
    sha sh;
    shs_init(&sh);

    add_to_hash(sh, temp_m);
    add_to_hash(sh, b);
    add_to_hash(sh, a);
    list_to_Big(sh, pi_L);
    list_to_Big(sh, pi_R);
    ECn_to_Big(sh, c1);
    ECn_to_Big(sh, c2);

    Big c = finish_hash_to_group(params, sh);

    ECn lefteq1 = c * C.second;
    lefteq1 += tag.A.second;
    ECn spoint = tag.zs * params.G;
    pair<ECn, ECn> righteq1 = ElGamal_Enc(params, params.vk, spoint, tag.za);

    if (lefteq1 != righteq1.second)
    {
        cout << "tag proof verify eq1 is uneq!" << endl;
        return false;
    }

    ECn lefteq2 = c * tag.d.second;
    lefteq2 += tag.B.second;
    //ECn spoint = tag.zs * params.G;
    pair<ECn, ECn> righteq2 = ElGamal_Enc(params, params.ek, spoint, tag.zb);

    if (lefteq2 != righteq2.second)
    {
        cout << "tag proof verify eq2 is uneq!" << endl;
        return false;
    }
    return true;
}

sigma full_sign(KeyParams& params, vector<ECn>& pk_list, char* m, Big& sk, int k){
    
    basic_sigma bsigma;
    bsigma = basic_sign(params, pk_list, sk, k, m);

    ECn R = bsigma.R;
    Big z = bsigma.z;
    Big r1 = bsigma.r1;
    vector<Big> c_array = bsigma.c_array;
    pair<ECn, ECn> C = bsigma.C;
    Big c_number = bsigma.c_number;
    vector<ECn> new_pk_list = bsigma.new_pk_list;

    ECn P = R;
    //ECn temp = -();
    P -= z * params.vk;
    vector<Big> a(c_array);
    NISA pi = NISA_Proof(params, new_pk_list, P, c_number, a);
    // tag proof
    Tag tag = tag_proof(params, pk_list[k], sk, r1, C, pi, m);

    return { c_array, z, R, C, pi, tag };
}

bool full_verify(KeyParams& params, vector<ECn>& pk_list, char* m, sigma& fsigma) {
    vector<ECn> new_pk_list(pk_list.size());

    pair<ECn, ECn> C = fsigma.C;
    ECn R = fsigma.R;
    Big z = fsigma.z;
    NISA pi = fsigma.pi;
    Tag tag = fsigma.tag;
    //Big c_value = fsigma.c_number;
    //ECn PP = fsigma.P;

    ECn c2 = C.second;
    for (int i = 0; i < pk_list.size(); i++)
    {
        
        new_pk_list[i] = c2;
        new_pk_list[i] -= pk_list[i];
    }

    Big temp_m = H1(m);
    sha sh;
    shs_init(&sh);
    
    add_to_hash(sh, temp_m);
    list_to_Big(sh, new_pk_list);
    ECn_to_Big(sh, R);

    Big c_number = finish_hash_to_group(params, sh);

    /*if (c_number == c_value)
    {
        cout << "the c_number is eq" << endl;
    }*/

    ECn P = R;
    P -= (z * params.vk);
    /*if (P == PP)
    {
        cout << "the P is eq" << endl;
    }*/

    if (!NISA_Verify(params,new_pk_list, P, c_number,pi))
    {
        cout << "NISA verify faliure!" << endl;
        return false;
    }
    //tag verify
    if (!tag_verify(params, C, pi, m, tag))
    {
        cout << "tag verify faliure!" << endl;
        return false;
    }
    return true;
}



Open opener_open(KeyParams& params, Big& dk, ECn& pk, vector<ECn>& pk_list, char* m, sigma& fsigma) {
    //bool bl = full_verify(params, pk_list, m, fsigma);
    //if (!bl)
    //{
    //    cout << "The signature is invalid!!!" << endl;
    //    //return;
    //}
	Big a = rand(params.q);
    ECn A = a * params.G;
    pair<ECn, ECn> C = fsigma.C;
    ECn c1 = C.first;
    ECn c2 = C.second;
    //ECn pk = ElGamal_Dec(params, dk, c1, c2);
    ECn B = a * c1;

    sha sh;
    shs_init(&sh);

    ECn_to_Big(sh, A);
    ECn_to_Big(sh, B);
    ECn_to_Big(sh, pk);

    Big c = finish_hash_to_group(params, sh);

    Big z = dk * c + a;

    return {pk, A, B, z};

}

bool open_verify(KeyParams& params, Open& open, vector<ECn>& pk_list, char* m, sigma& fsigma) {
    /*bool bl = full_verify(params, pk_list, m, fsigma);
    if (!bl)
    {
        cout << "The signature is invalid!!!" << endl;
        return false;
    }*/
    pair<ECn, ECn> C = fsigma.C;
    ECn c1 = C.first;
    ECn c2 = C.second;
    ECn A = open.A;
    ECn B = open.B;
    ECn pk = open.pk;
    Big z = open.z;

    sha sh;
    shs_init(&sh);

    ECn_to_Big(sh, A);
    ECn_to_Big(sh, B);
    ECn_to_Big(sh, pk);

    Big c = finish_hash_to_group(params, sh);

    ECn lefteq1 = c * params.vk;
    lefteq1 += A;
    ECn righteq1 = z * params.G;
    if (lefteq1 != righteq1)
    {
        cout << "NIZK proof verify eq1 is faliure!!!" << endl;
        return false;
    }

    ECn lefteq2 = c2;
    lefteq2 -= pk;
    lefteq2 *= c;
    lefteq2 += B;
    ECn righteq2 = z * c1;
    if (lefteq2 != righteq2)
    {
        cout << "NIZK proof verify eq2 is faliure!!!" << endl;
        return false;
    }
    return true;
}

pair<Big, Big> ecdsa_sign(KeyParams& params, char* m, Big sk) {
    ECn G = params.G;
    Big q = params.q;
    Big k = rand(q);
    G *= k;            /* see ebrick.cpp for technique to speed this up */
    Big x, y;
    G.get(x);
    x %= q;

    Big h = H1(m);

    /* calculate s */
    k = inverse(k, q);
    Big s = ((h + sk * x) * k) % q;
    return { x, s };
}

bool ecdsa_verify(KeyParams& params, char* m, ECn& C1, pair<Big, Big>& sigma) {
    Big q = params.q;
    ECn G = params.G;
    Big x = sigma.first;
    Big s = sigma.second;
    Big h = H1(m);
    s = inverse(s, q);
    Big u1 = (h * s) % q;
    Big u2 = (x * s) % q;
    ECn tmp1 = G;
    ECn tmp2 = C1;
    tmp1 *= u1;
    tmp2 *= u2;
    tmp1 += tmp2;
    Big r;
    tmp1.get(r);
    if (r % q == x)
    {
        return true;
    }
    return false;
}

void test_trial(KeyParams& params, Big dk) {
    vector<double> sign_time_list;
    vector<double> trace_time_list;
    vector<double> verify_time_list;
    vector<double> entire_time_list;
    vector<double> openproof_time_list;
    vector<double> openverify_time_list;
    vector<double> ecdsa_sign_time_list;
    vector<double> ecdsa_verify_time_list;

    cout << "power\tsign\tverify\ttrace\topenproof\topenverify\tecdsasign\tecdsaverify\tentire(ms)" << endl;

    for (int power = 1; power < 6; power++) {
        double sign_time_sum = 0;
        double trace_time_sum = 0;
        double verify_time_sum = 0;
        double entire_time_sum = 0;
        double openproof_time_sum = 0;
        double openverify_time_sum = 0;
        double ecdsa_sign_time_sum = 0;
        double ecdsa_verify_time_sum = 0;
        int power_of_2 = power + 1;
        int PK_num = (int)pow(2, power_of_2);
        int time_trail = 10;

        vector<ECn> fake_Pid(PK_num);
        vector<Big> fake_Ssk(PK_num);


        for (int j = 0; j < PK_num; j++) {
            KeyGen(params, fake_Ssk[j], fake_Pid[j]);
        }

        time_t seed;
        time(&seed);
        irand((long)seed);
        

        for (int ii = 0; ii < time_trail; ii++) {
            clock_t start_time = clock();
            int random_position = rand(params.q) % PK_num;
            //int random_position = 0;
            ECn pid;
            Big psk;
            KeyGen(params, psk, pid);
            fake_Pid[random_position] = pid;

            vector<Big> c_array(PK_num);
            vector<Big> a(PK_num);
            Big z = 0, c_number = 0, r1 = 0;
            ECn R;
            pair<ECn, ECn> C;
            vector<ECn> new_pk_list(PK_num);
            /*const char* message;
            message = new char[13];
            message = "I am a girl";*/
            
            clock_t sign_start_time = clock();
            //basic_sigma bsigma = basic_sign(params, fake_Pid, psk, random_position, (char *)"I am a girl");
            sigma fsigma = full_sign(params, fake_Pid, (char*)"I am a girl", psk, random_position);
            clock_t sign_end_time = clock();
            sign_time_sum += ((double)sign_end_time - (double)sign_start_time) / CLOCKS_PER_SEC;

            clock_t trace_start_time = clock();
            ECn pk = ElGamal_Dec(params, dk, fsigma.C.first, fsigma.C.second);
            //Open open = opener_open(params, dk, pk, fake_Pid, (char*)"I am a girl",  fsigma);
            clock_t trace_end_time = clock();
            trace_time_sum += ((double)trace_end_time - (double)trace_start_time) / CLOCKS_PER_SEC;

            clock_t openproof_start_time = clock();
            //ECn pk = ElGamal_Dec(params, dk, fsigma.C.first, fsigma.C.second);
            Open open = opener_open(params, dk, pk, fake_Pid, (char*)"I am a girl", fsigma);
            clock_t openproof_end_time = clock();
            openproof_time_sum += ((double)openproof_end_time - (double)openproof_start_time) / CLOCKS_PER_SEC;

            clock_t openverify_start_time = clock();
            if (!open_verify(params, open, fake_Pid, (char*)"I am a girl", fsigma)) {
                cout << "Open verify failed" << endl;
            }
            clock_t openverify_end_time = clock();
            openverify_time_sum += ((double)openverify_end_time - (double)openverify_start_time) / CLOCKS_PER_SEC;
            

            clock_t verify_start_time = clock();
            /*if (!basic_verify(params, (char *)"I am a girl", fake_Pid, bsigma)) {
                cout << "failed" << endl;
            }*/
            if (!full_verify(params, fake_Pid, (char*)"I am a girl", fsigma)) {
                cout << "full verify failed" << endl;
            }
            
            clock_t verify_end_time = clock();
            verify_time_sum += ((double)verify_end_time - (double)verify_start_time) / CLOCKS_PER_SEC;

            /*clock_t trace_start_time = clock();
            char* VIDk = trace(params, pfc, tag, fake_Pid, VID);
            clock_t trace_end_time = clock();
            trace_time_sum += ((double)trace_end_time - (double)trace_start_time) / CLOCKS_PER_SEC;*/

            Big sk = rand(params.q);
            ECn C1 = params.G;
            C1 *= sk;
            pair<Big, Big> ecsigma;
            clock_t ecdsa_sign_start_time = clock();
            //basic_sigma bsigma = basic_sign(params, fake_Pid, psk, random_position, (char *)"I am a girl");
            ecsigma = ecdsa_sign(params, (char*)"I am a girl", sk);
            clock_t ecdsa_sign_end_time = clock();
            ecdsa_sign_time_sum += ((double)ecdsa_sign_end_time - (double)ecdsa_sign_start_time) / CLOCKS_PER_SEC;

            clock_t ecdsa_verify_start_time = clock();
            /*if (!basic_verify(params, (char *)"I am a girl", fake_Pid, bsigma)) {
                cout << "failed" << endl;
            }*/
            if (!ecdsa_verify(params, (char*)"I am a girl", C1, ecsigma)) {
                cout << "ecdsa verify failed" << endl;
            }

            clock_t ecdsa_verify_end_time = clock();
            ecdsa_verify_time_sum += ((double)ecdsa_verify_end_time - (double)ecdsa_verify_start_time) / CLOCKS_PER_SEC;

            clock_t end_time = clock();
            entire_time_sum += ((double)end_time - (double)start_time) / CLOCKS_PER_SEC;
        }

        cout << power + 1 << "\t" << (sign_time_sum / time_trail) * 1000 << "\t" << (verify_time_sum / time_trail) * 1000
			<< "\t" << (trace_time_sum / time_trail) * 1000 << "\t" << (openproof_time_sum / time_trail) * 1000 << "\t" << (openverify_time_sum / time_trail) * 1000 << "\t" << (ecdsa_sign_time_sum / time_trail) * 1000 << "\t" << (ecdsa_verify_time_sum / time_trail) * 1000 << "\t" << (entire_time_sum / time_trail) * 1000 << endl;

        sign_time_list.push_back((sign_time_sum / time_trail) * 1000);
        trace_time_list.push_back((trace_time_sum / time_trail) * 1000);
        verify_time_list.push_back((verify_time_sum / time_trail) * 1000);
        openproof_time_list.push_back((openproof_time_sum / time_trail) * 1000);
        openverify_time_list.push_back((openverify_time_sum / time_trail) * 1000);
        entire_time_list.push_back((entire_time_sum / time_trail) * 1000);
        ecdsa_sign_time_list.push_back((ecdsa_sign_time_sum / time_trail) * 1000);
        ecdsa_verify_time_list.push_back((ecdsa_verify_time_sum / time_trail) * 1000);
    }

    // Get current date
    std::time_t t = std::time(nullptr);
    std::tm now;
    localtime_s(&now, &t);

    // Format date as YYYY-MM-DD
    std::ostringstream date_stream;
    date_stream << (now.tm_year + 1900) << '-'
        << (now.tm_mon + 1) << '-'
        << now.tm_mday << '-' << now.tm_hour << '-' << now.tm_min << '-';
    std::string date_str = date_stream.str();

    // Create filename with date
    std::string filename = date_str + "DualRing Ring Signature Time Analysis .txt";
    // 指定文件路径
    std::string directory = "D:\\VS2019\\repo\\2024-6-8-DualRing\\time_test\\";
    //std::string filename = "output.txt";
    std::string filepath = directory + filename;

    // Writing to file
    std::ofstream text_file;
    text_file.open(filepath);
    if (!text_file.is_open()) {
        std::cerr << "Failed to open file: " << filename << std::endl;
        //return 1;
    }

    // writing to file
    //ofstream text_file("DualRing Ring Signature Time Analysis.txt");
    text_file << "2^n\tSign\tVerify\tTrace\tOpenpr\tOpenver\tECSign\tECVerify\n";
    for (size_t i = 0; i < sign_time_list.size(); i++) {
        text_file << i + 1 << "\t" << sign_time_list[i] << "\t" << verify_time_list[i] << "\t" << trace_time_list[i] << "\t" << openproof_time_list[i] << "\t" << openverify_time_list[i] << "\t" << ecdsa_sign_time_list[i] << "\t" << ecdsa_verify_time_list[i] << endl;
    }
    text_file.close();
}

int main()
{
    ifstream common("secp160.ecs");    /* construct file I/O streams */
    /*ofstream public_key("public.ecs");
    ofstream private_key("private.ecs");*/
    int bits, ep;
    miracl* mip = &precision;

    ECn G, W, Q;
    Big a, b, p, q, x, y, d;

    time_t seed;
    time(&seed);
    irand((long)seed);

    common >> bits;
    mip->IOBASE = 16;
    common >> p >> a >> b >> q >> x >> y;
    mip->IOBASE = 10;

    ecurve(a, b, p, MR_PROJECTIVE);

    if (!G.set(x, y))
    {
        cout << "Problem - point (x,y) is not on the curve" << endl;
        return 0;
    }
    ECn vk, ek, u;
    Big dk = rand(q);
    Big u_rand = rand(q);
    Big tau = rand(q);
    
    vk = dk * G;
    ek = tau * G;
    u = u_rand * G;
    KeyParams params;
    params.G = G;
    params.q = q;
    params.ek = ek;
    params.vk = vk;
    params.u = u;

    test_trial(params, dk);

    return 0;
}

