
AutoDeclare Functions sd;
AutoDeclare Symbol z;
Functions  n,m x, y, e, f, k, K, ki, Ki, S, TT, T, co, an, Sch, AT, a, A, b ,B, R;
CFunctions qi, q, Q, xf, xfi, c1, c2, sq, sqi, sf, sfi, H , P;
******************************************************
********* TESTING COPRODUCT BRAIDED MORPHISM *********
********* FOR U_q(su(2)) *****************************
******************************************************
**** xf  =  e^{-4i\phi}
**** xfi =  e^{4i\phi}
**** qi = 1/q
**** K = k*, ki = k^{-1}
***************************************************
********** CHECKING Uqsu(2) brading
******************************************************
Local d1 = co(e)*S*co(k) - q*xf*co(k)*S*co(e);
Local d2 = co(e)*S*co(K) - q*xfi*co(K)*S*co(e);
Local d3 = co(f)*S*co(k) - qi*xfi*co(k)*S*co(f);
Local d4 = co(f)*S*co(K) - qi*xf*co(K)*S*co(f);
Local d5 = (co(e)*S*co(f) - co(f)*S*co(e)) - P*(co(k)*S*co(K) - co(ki)*S*co(Ki));
***************************************************
********** CHECKING Uqsu(2) representation
***************************************************
Local w11 = (e*k-q*xf*k*e)*a;
Local w21 = (e*K-q*xfi*K*e)*a;
Local w31 = (f*k-qi*xfi*k*f)*a;
Local w41 = (f*K-qi*xf*K*f)*a;
Local w51 = (e*f - f*e - P*(k*K-ki*Ki))*a;
Local w12 = (e*k-q*xf*k*e)*A;
Local w22 = (e*K-q*xfi*K*e)*A;
Local w32 = (f*k-qi*xfi*k*f)*A;
Local w42 = (f*K-qi*xf*K*f)*A;
Local w52 = (e*f - f*e - P*(k*K-ki*Ki))*A;
Local w13 = (e*k-q*xf*k*e)*b;
Local w23 = (e*K-q*xfi*K*e)*b;
Local w33 = (f*k-qi*xfi*k*f)*b;
Local w43 = (f*K-qi*xf*K*f)*b;
Local w53 = (e*f - f*e - P*(k*K-ki*Ki))*b;
Local w14 = (e*k-q*xf*k*e)*B;
Local w24 = (e*K-q*xfi*K*e)*B;
Local w34 = (f*k-qi*xfi*k*f)*B;
Local w44 = (f*K-qi*xf*K*f)*B;
Local w54 = (e*f - f*e - P*(k*K-ki*Ki))*B;
***************************************************
********** CHECKING Uqsu(2) action
***************************************************
Local z11 = co(e)*R*(a*b-q*xfi*b*a);
Local z12 = co(e)*R*(a*B-q*xf*B*a);
Local z13 = co(e)*R*(b*B-B*b);
Local z14 = co(e)*R*(b*A-q*xfi*A*b);
Local z15 = co(e)*R*(B*A-q*xf*A*B);
Local z16 = co(e)*R*(a*A+q*q*b*B);
Local z17 = co(e)*R*(A*a+b*B);
Local z21 = co(f)*R*(a*b-q*xfi*b*a);
Local z22 = co(f)*R*(a*B-q*xf*B*a);
Local z23 = co(f)*R*(b*B-B*b);
Local z24 = co(f)*R*(b*A-q*xfi*A*b);
Local z25 = co(f)*R*(B*A-q*xf*A*A);
Local z26 = co(f)*R*(a*A+q*q*b*B);
Local z27 = co(f)*R*(A*a+b*B);
**************************************************
repeat;
id co(k) = k*T*k;
id co(K) = K*T*K;
id co(ki) = ki*T*ki;
id co(Ki) = Ki*T*Ki;
id co(e) = e*T*k + ki*T*e;
id co(f) = f*T*K + Ki*T*f;
endrepeat;
**************************************************
repeat;
id x?*S*y? = H(x,y)*y*TT*x;
endrepeat;
**************************************************
******* BRAIDING
**************************************************
repeat;
id H(k, x?) = 1;
id H(K, x?) = 1;
id H(ki, x?) = 1;
id H(Ki, x?) = 1;
id H(x?, k) = 1;
id H(x?, K) = 1;
id H(x?, ki) = 1;
id H(x?, Ki) = 1;
id H(e,f) = xf*xf;
id H(f,e) = xf*xf;
id H(e,e) = xfi*xfi;
id H(f,f) = xfi*xfi;
endrepeat;
**************************************************
******* BRAIDING
**************************************************
repeat;
id T*e*R*b = P(e,b)*b*T*e;
id T*f*R*b = P(f,b)*b*T*f;
id T*e*R*B = P(e,B)*B*T*e;
id T*f*R*B = P(f,B)*B*T*f;
id T*x?*R*y? = y*T*x;
endrepeat;
.sort
**************************************************
*** ACTION RULES
**************************************************
repeat;
id e*a = 0;
id e*A = b;
id e*b = 0;
id e*B = -qi*xf*a;
id f*a = -q*xfi*B;
id f*A = 0;
id f*b = A;
id f*B = 0;
id k*a = sqi*sfi*a;
id k*A = sq*sf*A;
id k*b = sqi*sfi*b;
id k*B = sq*sf*B;
id ki*a = sq*sf*a;
id ki*A = sqi*sfi*A;
id ki*b = sq*sf*b;
id ki*B = sqi*sfi*B;
id K*a = sqi*sf*a;
id K*A = sq*sfi*A;
id K*b = sqi*sf*b;
id K*B = sq*sfi*B;
id Ki*a = sq*sfi*a;
id Ki*A = sqi*sf*A;
id Ki*b = sq*sfi*b;
id Ki*B = sqi*sf*B;
id xf=sf*sf;
id xfi=sfi*sfi;
endrepeat;
**************************************************
id T=1; ******** MULTIPLICATION ******************
**************************************************
****** APPLYING ALGEBRA RULES
**************************************************
repeat;
id e*k = q*xf*k*e;
id e*K = q*xfi*K*e;
id e*ki = qi*xfi*ki*e;
id e*Ki = qi*xf*Ki*e;
id e*f = f*e + P*(k*K - Ki*ki);
**************************************************
id f*k = qi*xfi*k*f;
id f*K = qi*xf*K*f;
id f*ki = q*xf*ki*f;
id f*Ki = q*xfi*Ki*f;
id K*k = k*K;
id Ki*ki = ki*Ki;
id Ki*K = 1;
id ki*k = 1;
id K*Ki = 1;
id k*ki = 1;
id Ki*k = k*Ki;
id ki*K = K*ki;
**************************************************
id b*a = qi*xf*a*b;
id B*a = qi*xfi*a*B;
id b*B = B*b;
id b*A = q*xfi*A*b;
id B*A = q*xf*A*B;
id a*A = 1- q*q*b*B;
id A*a = 1- b*B;
**************************************************
id q = sq*sq;
id qi=sqi*sqi;
id xf=sf*sf;
id xfi=sfi*sfi;
id sq*sqi=1;
id sf^n?*sfi^m?=sf(n-m);
id P*sqi^2 = 1 + sq^2*P;
id xf=sf*sf;
id xfi=sfi*sfi;
endrepeat;
id P(e,b)=sfi^4;
id P(f,b)=sf^4;
id P(e,B)=sf^4;
id P(f,B)=sfi^4;
.sort
repeat;
id sf*sfi^2=sfi;
id sf^2*sfi=sf;
id sf*sfi=1;
endrepeat;
**************************************************
.sort
Bracket k,K,e,f;
Print;
.end
