//Context Free Grammar (LL(1)) parser

//Grammar needs to be in Variable->production rule structure
//We can make a graph where each variable node is connected to its production rule characters
//The following implementation only considers ASCII characters (doesn't support UTF-8)

//Epsilon or empty is represented by '#' symbol

#include <iostream>
#include <unordered_map>
#include <vector>
#include <unordered_set>

using namespace std;

//Base class for all CFG parser types
class ContextFreeGrammar
{

private:
    //Store the starting symbol then we don't need to keep production rules in order
    char startSymbol;

protected:
    //Adjacency list representation of graph
    unordered_map<char, vector<vector<char>>> cfgGraph;

public:
    //Default constructor
    ContextFreeGrammar()
    {
    }

    void setStartSymbol(char startSymbol)
    {
        this->startSymbol = startSymbol;
    }

    char getStartSymbol()
    {
        return startSymbol;
    }

    void setCfgGraph(unordered_map<char, vector<vector<char>>> cfgGraph)
    {
        this->cfgGraph = cfgGraph;
    }

    unordered_map<char, vector<vector<char>>> getCfgGraph()
    {
        return cfgGraph;
    }

    //Print the given context free grammar
    void showCfgGraph()
    {

        for (auto it = cfgGraph.begin(); it != cfgGraph.end(); ++it)
        {
            cout << it->first << " -> ";

            for (int i = 0, n = it->second.size(); i < n; ++i)
            {

                for (int j = 0, m = it->second[i].size(); j < m; ++j)
                {
                    cout << it->second[i][j];
                }

                if (i != n - 1)
                    cout << " / ";
            }

            cout << endl;
        }
    }
};

//LL1 parser class
class LL1 : public ContextFreeGrammar
{
protected:
    //Store FIRST of non-terminals
    unordered_map<char, unordered_set<char>> firstTable;
    //Store FOLLOW of non-terminals
    unordered_map<char, unordered_set<char>> followTable;

    unordered_map<char, unordered_map<char, int>> predictionTable;

public:
    //Default constructor
    LL1()
    {
    }

    void FIRST(char nonTerminal)
    {
        if (firstTable.find(nonTerminal) != firstTable.end())
            return;

        vector<char> stack = {nonTerminal};

        /*
                The character we are pushing on stack can lead to epsilon (#)
                    keeping the origin vector as parent of this character
                    we can take first of next chanracter in parent
            */
        unordered_map<char, vector<char>> parent;

        //DFS over current nonTerminal in cfgGraph
        while (stack.size() > 0)
        {
            char current = stack.back();
            stack.pop_back();
            // cout << endl;
            // cout << current << " popped" << endl;
            for (int i = 0, n = this->cfgGraph[current].size(); i < n; ++i)
            {

                //store iterated character
                char temp = this->cfgGraph[current][i][0];

                //Check if iterated character is terminal
                if (this->cfgGraph.find(temp) == this->cfgGraph.end())
                {

                    //Check if the terminal already exists in FIRST of current
                    if (this->firstTable[nonTerminal].find(temp) == this->firstTable[nonTerminal].end())
                    {

                        //We reached epsilon(#) so we need to consider first of next character in parent vector
                        if (temp == '#')
                        {

                            //Check if parent vector has next character and that is terminal
                            if (parent[current].size() > 0 and this->cfgGraph.find(parent[current][0]) == this->cfgGraph.end())
                                this->firstTable[nonTerminal].insert(parent[current][0]);

                            //The next character in parent is non-terminal so push it on stack
                            else if (parent[current].size() > 0)
                            {
                                stack.push_back(parent[current][0]);
                                vector<char> parentVector(parent[current].begin() + 1, parent[current].end());
                                parent[parent[current][0]] = parentVector;
                            }

                            //Assuming we reached end of the vector so just insert epsilon(#)
                            else
                            {
                                this->firstTable[nonTerminal].insert(temp);
                            }
                        }

                        else
                            this->firstTable[nonTerminal].insert(temp);
                    }
                }

                else
                {

                    stack.push_back(temp);
                    vector<char> parentVector(this->cfgGraph[current][i].begin() + 1, this->cfgGraph[current][i].end());
                    parent[temp] = parentVector;
                }
            }
        }
    }

    void FOLLOW(char nonTerminal)
    {
        vector<char> stack = {nonTerminal};
        char current;
        while (stack.size() > 0)
        {
            current = stack.back();
            stack.pop_back();

            for (auto it = this->cfgGraph.begin(); it != this->cfgGraph.end(); ++it)
            {
                for (int i = 0; i < it->second.size(); ++i)
                {
                    bool flag = 0;
                    for (int j = 0; j < it->second[i].size(); ++j)
                    {
                        if (it->second[i][j] == current)
                        {
                            flag = 1;
                        }
                        else if (flag)
                        {
                            if (this->cfgGraph.find(it->second[i][j]) == this->cfgGraph.end())
                            {
                                if (it->second[i][j] != '#')
                                {
                                    followTable[nonTerminal].insert(it->second[i][j]);
                                    flag = 0;
                                }
                            }
                            else
                            {

                                if (this->firstTable[it->second[i][j]].find('#') == this->firstTable[it->second[i][j]].end())
                                {
                                    this->followTable[nonTerminal].insert(firstTable[it->second[i][j]].begin(), firstTable[it->second[i][j]].end());

                                    flag = 0;
                                }
                                else
                                {
                                    for (auto k = this->firstTable[it->second[i][j]].begin(); k != this->firstTable[it->second[i][j]].end(); ++k)
                                    {
                                        if (*k == '#')
                                            continue;
                                        this->followTable[nonTerminal].insert(*k);
                                    }
                                }
                            }
                        }
                        if (flag and j == it->second[i].size() - 1)
                        {

                            followTable[nonTerminal].insert(followTable[it->first].begin(), followTable[it->first].end());
                            if (it->first != current and it->first != nonTerminal)
                                stack.push_back(it->first);
                        }
                    }
                }
            }
        }
    }

    void makeParsingTable()
    {

        for (auto it = this->cfgGraph.begin(); it != this->cfgGraph.end(); ++it)
        {

            for (int i = 0; i < it->second.size(); ++i)
            {

                char firstOfRhs = it->second[i][0];
                //First of RHS is terminal or empty
                if (this->cfgGraph.find(firstOfRhs) == this->cfgGraph.end())
                {
                    if (firstOfRhs == '#')
                    {
                        for (auto k = followTable[it->first].begin(); k != followTable[it->first].end(); ++k)
                        {
                            predictionTable[it->first][*k] = i;
                        }
                    }
                    else
                        predictionTable[it->first][firstOfRhs] = i;
                }
                //First of RHS is non-terminal
                else
                {
                    //FIRST(RHS) doesn't contain empty
                    if (firstTable[firstOfRhs].find('#') != firstTable[firstOfRhs].end())
                    {
                        for (auto k = followTable[firstOfRhs].begin(); k != followTable[firstOfRhs].end(); ++k)
                        {
                            predictionTable[it->first][*k] = i;
                        }
                    }
                    for (auto k = firstTable[firstOfRhs].begin(); k != firstTable[firstOfRhs].end(); ++k)
                    {
                        if (*k != '#')
                            predictionTable[it->first][*k] = i;
                    }
                }
            }
        }
    }

    //Call FIRST for all non-terminals
    void makeFirstTable()
    {

        for (auto it = this->cfgGraph.begin(); it != this->cfgGraph.end(); ++it)
        {
            FIRST(it->first);
        }
    }

    //Call FOLLOW for all non-terminals
    void makeFollowTable()
    {

        followTable[this->getStartSymbol()].insert('$');

        for (auto it = this->cfgGraph.begin(); it != this->cfgGraph.end(); ++it)
        {
            FOLLOW(it->first);
        }
    }

    void showFirstTable()
    {
        for (auto it = this->firstTable.begin(); it != this->firstTable.end(); ++it)
        {
            cout << "FIRST(" << it->first << "): ";
            for (auto j = it->second.begin(); j != it->second.end(); ++j)
            {
                cout << *j << " ";
            }
            cout << endl;
        }
    }

    void showFollowTable()
    {
        for (auto it = this->followTable.begin(); it != this->followTable.end(); ++it)
        {
            cout << "FOLLOW(" << it->first << "): ";
            for (auto j = it->second.begin(); j != it->second.end(); ++j)
            {
                cout << *j << " ";
            }
            cout << endl;
        }
    }

    void showParsingTable()
    {
        for (auto it = this->predictionTable.begin(); it != this->predictionTable.end(); ++it)
        {

            cout << it->first << ": " << endl;
            cout << endl;
            for (auto i = it->second.begin(); i != it->second.end(); ++i)
            {

                cout << i->first << ": " << it->first << " -> ";

                for (int j = 0; j < this->cfgGraph[it->first][i->second].size(); ++j)
                {
                    cout << this->cfgGraph[it->first][i->second][j];
                }
                cout << endl;
            }
            cout << endl;
        }
    }
};

LL1 inputGrammar()
{

    LL1 obj;
    unordered_map<char, vector<vector<char>>> productionRules;
    char inputCharacter;

    bool continueInput = true;

    string inputString;

    cout << "Start symbol: ";
    cin >> inputCharacter;

    obj.setStartSymbol(inputCharacter);

    cout << "Enter production rules:" << endl;
    while (continueInput)
    {
        cout << inputCharacter << " > ";

        //Input string mapped to non-terminal
        cin >> inputString;

        vector<char> temp; //temporary vector to store characters mapped to non-terminal

        for (int i = 0, n = inputString.size(); i < n; ++i)
        {
            temp.push_back(inputString[i]);
        }

        //map the production vector to its non-terminal
        productionRules[inputCharacter].push_back(temp);

        //Clear temporary vector for next non-terminal input
        temp.clear();

        cout << "Continue input for next variable?(y/n): ";
        cin >> inputCharacter;

        if (inputCharacter == 'y' || inputCharacter == 'Y')
        {

            //Set input condition to true to keep the while loop going
            continueInput = true;

            cout << "Input variable: ";

            //Take non-terminal input
            cin >> inputCharacter;
        }
        else if (inputCharacter == 'n' or inputCharacter == 'N')
        {
            continueInput = false;
            cout << endl;
        }
        else
        {
            cout << "Invalid Choice!" << endl;
            exit(0);
        }
    }
    obj.setCfgGraph(productionRules);
    return obj;
}

int main()
{

    LL1 parser = inputGrammar();
    parser.showCfgGraph();
    parser.makeFirstTable();

    cout << endl;
    parser.showFirstTable();

    cout << endl;
    parser.makeFollowTable();
    parser.showFollowTable();

    cout << endl;
    parser.makeParsingTable();
    parser.showParsingTable();
    return 0;
}
