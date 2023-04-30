#include<bits/stdc++.h>
#include "sha256.h"
using namespace std;

class Block;
class Blockchain;
class Node;
class Endorsers;
class Orderers;
class Committers;
class MSP;

void printBlock(Block &b);
void printChain(Blockchain &BC);

//////////////////////////////////////////    Class BLOCK    ///////////////////////////////////////////////

class Block{

    public :

    vector<string> spam_calls;
    int nonce;
    string hash, prev_hash;
    time_t timestamp;

    Block() : spam_calls({}), prev_hash(""), hash(""), nonce(0), timestamp(time(nullptr)) {}

    Block(vector<string> spam_calls, string prev_hash, int nonce = 0) 
    {
        this->spam_calls = spam_calls;
        this->prev_hash = prev_hash;
        this->timestamp = time(nullptr);
        this->nonce = nonce;
        this->hash = calculateHash();
    }

    string combine_hash(string s1, string s2)
    {
        string str = s1 + s2;
        return sha256(str);
    }

    void build_MerkleTree(vector<string> &t, int v, int tl, int tr, vector<string> &A)
    {
        if(tl == tr)
        {
            t[v] = sha256(A[tl]); return;
        }
        int tm = (tl+tr)/2;
        build_MerkleTree(t, 2*v+1, tl, tm, A);
        build_MerkleTree(t, 2*v+2, tm+1, tr, A);
        t[v] = combine_hash(t[2*v+1], t[2*v+2]);
    }

    string calculateHash() 
    {
        int i,j,n=spam_calls.size();
        if(n<=0) return string(64,'0');
        vector<string> A(n), t(4*n);
        for(i=0;i<n;i++)
        {
            A[i] = spam_calls[i] + to_string(nonce) + to_string(timestamp);
        }
        build_MerkleTree(t,0,0,n-1,A);
        return t[0];                        // Returning hash on Markle root
    }

};

//--------------------------------------------------------------------------------------------------------------

//////////////////////////////////////////    Class BLOCKCHAIN    ///////////////////////////////////////////////

class Blockchain{

    public :

    vector<Block> chain;

    Blockchain() 
    {
        chain.push_back(Block({},string(64,'0')));
    }

    Block& getLatestBlock() 
    {
        return chain.back();
    }

    void addBlock(Block& newBlock) 
    {
        newBlock.prev_hash = getLatestBlock().hash;
        chain.push_back(newBlock);
    }
} Hyperledger;

//------------------------------------------------------------------------------------------------------

///////////////////////////////////   CONSENSUS MECHANISM   ////////////////////////////////////////
////////////////////////////  Crash tolerant consensus mechanism   /////////////////////////////////
bool consensus()
{
    // Each orderer O[i] has a set V[i]
    // Each O[i] will also send S[k][i] in kth round
    // V[i] = V[i] U S[k][j] for all j != i

    int n=10, f=3;
    set<int> V[n], S[f+2][n], Sent[n];
    vector<int> res(n);
    for(int i=0; i<n; i++) V[i].insert(1);

    // V[0..2] are faulty / crash prone
    vector<int> r(f);
    for(int j=0; j<f; j++)
    {
        r[j] = 1 + rand()%(f+1);
    }

    for(int k=1; k<= f+1; k++)
    {
        for(int i=0; i<n; i++)               // Send msgs in round k
        {
            if(i<f && k>=r[i]) continue;     // Faulty nodes won't send anything after crash

            for(int v : V[i])
            {
                if(Sent[i].find(v) == Sent[i].end()) S[k][i].insert(v);
            }
        }

        for(int i=0; i<n; i++)               // Computation in round k
        {
            if(i<f && k>=r[i]) continue;     // Faulty nodes won't compute after crash

            for(int j=0; j<n; j++)
            {
                if(j==i) continue;
                for(int s : S[k][j])
                {
                    if(V[i].find(s) == V[i].end()) V[i].insert(s);
                }
            }
        }
    }

    for(int i=0; i<n; i++) res[i] = *(V[i].begin());
    for(int i=1; i<n; i++) 
    {
        if(res[i] != res[0]) return 0;
    }
    return 1;
}


//--------------------------------------------------------------------------------------------------

pair<int,int> calculate_mode(vector<int> &A)
{
    unordered_map<int,int> mp;
    map<int,vector<int> > rev_mp;
    for(int i=0;i<A.size();i++) mp[A[i]]++;

    for(auto x:mp)
    {
        rev_mp[(-1)*(x.second)].push_back(x.first);
    }

    auto it = rev_mp.begin();
    if((it->second).size() > 1) return {0,0};
    return {(it->second)[0], (-1)*(it->first)};
}


////////////////////////////////////   CONSENSUS MECHANISM   ////////////////////////////////////////
/////////////////////////  Byzantine fault tolerant consensus mechanism   //////////////////////////
bool byzantine_consensus()
{
    int n=10, f=2;
    vector<vector<int> > pref(n, vector<int> (n));

    for(int i=0;i<f;i++)              // Byzantine nodes are simulated by randomness
    {
        for(int j=0;j<n;j++) pref[i][j] = rand()%2;
    }

    for(int i=f;i<n;i++)
    {
        for(int j=0;j<n;j++) pref[i][j] = 0;
        pref[i][i] = 1;
    }

    vector<int> res(n), maj(n), mult(n);
    vector<vector<int> > received(n, vector<int> (n));
    
    for(int k=1; k<=f+1; k++)
    {
        for(int i=0;i<n;i++)
        {
            for(int j=0;j<n;j++)
            {
                pref[i][j] = pref[j][j];
                if(i<f || j<f) pref[i][j] = rand()%2;
            }
            pair<int,int> p = calculate_mode(pref[i]);
            maj[i] = p.first; mult[i] = p.second;
        }

        int king_maj=0;
        for(int i=0;i<n;i++)
        {
            king_maj = maj[k-1];      // kth processor is king of phase k

            if(mult[i] > (n/2 + f)) pref[i][i] = maj[i];
            else pref[i][i] = king_maj;

            if(k==f+1) res[i] = pref[i][i];
        }
    }

    for(int i=f; i<n; i++) 
    {
        if(res[i] != res[f]) return 0;   // All honest nodes must agree on same value
    }
    return 1;
}


//--------------------------------------------------------------------------------------------------

//////////////////////////  Class MSP - Membership Service Provider  //////////////////////////////

class MSP{

    public :

    unordered_map<string,string> reg;          // Owner has Database of IDs of people to check authenticity

    bool check_authority(string name, string Aadhaar_ID)
    {
        if(reg[Aadhaar_ID] == name) return true;
        cout<<"Sorry! Aadhaar ID not matching. Forfeiting request...\n\n";
        return false;
    }
};

//---------------------------------------------------------------------------------------------------
MSP Owner;
vector<string> spams;


//////////////////////////////////////      Class NODE     ///////////////////////////////////////////

class Node {

    private :
    vector<Block> personal_ledger;

    public :

    string name, Aadhaar_ID;

    Node() : name(""), Aadhaar_ID("") {}
    Node(string str, string id) 
    {
        this->name = str;
        this->Aadhaar_ID = id;
    }

    /////////////////////////////   Class ENDORSERS   /////////////////////////////
    class Endorsers {

        private : 
        unordered_map<string,int> count;

        public :

        int chaincode(string pno)
        {
            // Do something something for validation and return 0 or 1
            // e.g. checking something like : Is the phone no. even valid to proceed the proposal?
            // Has the no. been reported earlier? If yes, then just add count to that maybe

            ///////////////////////////////// Complete this //////////////////////////
            if(pno.length() != 10)
            {
                cout<<"Reported mobile number is invalid !\n"; return 0;
            }

            if(count.find(pno) != count.end())
            {
                count[pno]++;
                cout<<"This call is SPAM! Had been reported earlier. Blocking the call ... \n"; return 0;
            }

            return 1;
        }
    };
    Endorsers E[10];

    ////////////////////////////    Class ORDERERS    ///////////////////////////////
    class Orderers {

        public :

        //////////////////////    Class COMMITTERS    /////////////////////////
        class Committers {

            private :

            vector<Block> personal_ledger;

            public :

            Committers()
            {
                personal_ledger.push_back(Block({},"0"));
            }

            void commit()
            {
                Block newBlock;
                newBlock.spam_calls = spams;
                newBlock.prev_hash = (Hyperledger.getLatestBlock()).hash;
                newBlock.nonce = rand()%100;
                newBlock.timestamp = time(nullptr);
                newBlock.hash = newBlock.calculateHash();

                (Hyperledger.chain).push_back(newBlock);
                (this->personal_ledger).push_back(newBlock);
                cout<<"New Block added!! Blockchain size now = "<<(Hyperledger.chain).size()<<"\n\n";
                printChain(Hyperledger);
            }
        };
        Committers committer;
        //-----------------------------------------------------------------------------------------


        void order()
        {
            if(spams.size() < 3) 
            {
                sort(spams.begin(),spams.end());
                return;
            }
            // gain consensus on the order, and then send to committing nodes
            // Suppose the first three orderer nodes are faulty / Byzantine, and return results randomly
            // We'll support only crash failures, so suppose first three orderer nodes can crash

            cout<<"3 new requests collected. Put these into a new block and push into the Blockchain ...\n";
            cout<<"-------------------------------------------------------------------------------------\n";
            //if(consensus())
            if(byzantine_consensus())
            {
                cout<<"Consensus achieved!!\n";
                committer.commit();
                spams.clear();
            }

        }
    };
    Orderers O[10];
    //-----------------------------------------------------------------------------------------------

    void report(string pno, MSP& Owner)
    {
        cout<<"Client Name = "<<this->name<<"  Client ID = "<<this->Aadhaar_ID<<endl;
        bool valid_client = Owner.check_authority(this->name, this->Aadhaar_ID);
        if(!valid_client) return;
        cout<<"Authentic client. Aadhaar ID matched!\n";

        int yes = 0;
        for(int i=0;i<10;i++)
        {
            int vote = E[i].chaincode(pno);
            yes += vote;
        }
        if(yes < 10)
        {
            cout<<"Inappropriate request! Request not endorsed. Terminating... \n\n";
            return;
        }
        cout<<"Request endorsed. Proceeding with ordering the requests... \n\n";
        spams.push_back(pno);
        for(int i=0;i<10;i++)
        {
            O[i].order();
        }
    }

};

Node Peers[5];

//----------------------------------------------------------------------------------------------------

void printBlock(Block &b)
{
    cout<<"Spam calls : ";
    for(int i=0; i<(b.spam_calls).size(); i++) cout<<b.spam_calls[i]<<" | ";
    cout<<endl;
    cout<<"Nonce : "<<b.nonce<<" | Timestamp : "<<b.timestamp<<endl;
    cout<<"Previous hash : "<<b.prev_hash<<endl;
    cout<<"Current hash  : "<<b.hash<<endl;
}

void printChain(Blockchain &BC)
{
    cout<<"Genesis Block :\n";
    printBlock(BC.chain[0]);
    for(int i=1; i<BC.chain.size(); i++)
    {
        cout<<"\t\t\t^\t\t\t\n";
        cout<<"\t\t\t|\t\t\t\n";
        cout<<"Block "<<i<<" :\n";
        printBlock(BC.chain[i]);
    }
    cout<<endl;
    cout<<"-------------------------------------------------------------------------------------\n\n";
}


int main()
{

    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);

    unordered_map<string,string> ID_record;
    ID_record = {   {"0058", "Raushan"  },
                    {"0003", "Adarsh"   },
                    {"0033", "Pranav"   },
                    {"0005", "Altaf"    },
                    {"0006", "Amay"     },
                    {"0018", "Kaushik"  },
                    {"0057", "Harsh"    },
                    {"0052", "Yash"     },
                    {"0054", "Aditya"   },
                    {"0009", "Aviraj"   },
                    {"0014", "Gyan"     },
                    {"0008", "Archit"   },
                    {"0056", "Soumyajit"},
                    {"0044", "Shreyansh"},
                    {"0050", "Varun"    }
                };
    Owner.reg = ID_record;
    cout<<"-------------------------------------------------------------------------------------\n";
    cout<<"Register of identity records :\n";
    cout<<"-------------------------------------------------------------------------------------\n";
    for(auto x:Owner.reg)
    {
        cout<<x.first<<" -> "<<x.second<<endl;
    }
    cout<<endl;
    cout<<"-------------------------------------------------------------------------------------\n";

    Node client1("Raushan","0058"), client2("Adarsh","0003"), client3("Pranav","0033"), client4("Yash","0052"), 
         client5("Nikhil","0077"), client6("Federer","0020"), client7("Amay","0006");
    client1.report("1234567890", Owner);
    client2.report("1235567890", Owner);
    client3.report("1234577890", Owner);
    client7.report("1234567890", Owner);
    client4.report("2345678980", Owner);
    client5.report("6234567890", Owner);
    client6.report("6232567899", Owner);
    client7.report("9574884963", Owner);
    client2.report("8485126749", Owner);


    return 0;
}