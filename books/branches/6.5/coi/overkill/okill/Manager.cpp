// Overkill System for ACL2 Testing
// Written by Jared Davis 

#include "Manager.h"
#include "Worker.h"
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <getopt.h>


static void appendFileStrings (const string& filename, list<string>& ret)
{
    // dumps all strings from filename into the file ret.

    ifstream fin(filename.c_str());
    if (!fin.is_open()) {
	cerr << "Error opening file " << filename << endl;
	exit(1);
    }

    string file;
    while(fin >> file) {
	ret.push_back(file);
    }    

    fin.close();
}


static void appendFileLines (const string& filename, list<string>& ret)
{
    // dumps all lines from filename into the file ret.

    ifstream fin(filename.c_str());
    if (!fin.is_open()) {
	cerr << "Error opening file " << filename << endl;
	exit(1);
    }

    // why the hell doesn't getline return a string?
    char buf[5001];
    while(!fin.eof()) {
	fin.getline(buf, 5000);

	if (buf[0] != 0)       
	    ret.push_back(buf);
    }

    fin.close();
}



Manager::Manager(int argc, char** argv)
{
    parseOptions(argc, argv);
    pthread_mutex_init(&d_mutex, NULL);    

//    cout << "Reading books from " << d_cmdsFile << "... ";
    appendFileLines(d_cmdsFile, d_workList);
//    cout << d_workList.size() << " books to process." << endl;

//    cout << "Reading hosts from " << d_hostsFile << "... ";
    list<string> hosts;
    appendFileStrings(d_hostsFile, hosts);
//    cout << hosts.size() << " hosts to work with." << endl;

    // Create a worker for each host
    for(list<string>::iterator i = hosts.begin(); i != hosts.end(); ++i)    
	d_workers.push_back(new Worker(*this, *i));    

    // Delete the previous results file, if any
    string rm = "rm -f " + getLogFile();
    system(rm.c_str());
}


Manager::~Manager()
{
    list<Worker*>::iterator i;

    for(i = d_workers.begin(); i != d_workers.end(); ++i)
	delete *i;
}


void Manager::startWorkers()
{
    list<Worker*>::iterator i;

    // Start all workers on their jobs.
    for(i = d_workers.begin(); i != d_workers.end(); ++i)
    {
	Worker* worker = *i;
	worker->startWork();
    }

    // Wait until all workers finish.
    for(i = d_workers.begin(); i != d_workers.end(); ++i)
    {
	Worker* worker = *i;
	pthread_join(worker->getPid(), NULL);
    }
}


const string& Manager::getLogFile() const
{
    return d_logFile;
}


bool Manager::requestWork(const Worker& requestor, string& result)
{
    bool ret;

    pthread_mutex_lock(&d_mutex);

    if (d_workList.empty()) 
    {
	ret = false;
    }

    else 
    {
	ret = true;
	result = *(d_workList.begin());
	d_workList.pop_front();
    }

    pthread_mutex_unlock(&d_mutex);

    return ret;
}


void Manager::parseOptions(int argc, char** argv)
{
    struct option long_options[] = {
	{"cmds", 1, 0, 'b'},
	{"hosts", 1, 0, 'h'},
	{"log", 1, 0, 'r'}
    };

    const char* help = 
	"Overkill, v0.1\n"
	"Usage: overkill --cmds <cmds> --hosts <hosts> --log <log>\n\n"
	" -c, --cmds <cmds>    Which commands to execute.\n"
	" -h, --hosts <hosts>  Which hosts to use.\n"
        " -l, --log <log>      Where to write messages.\n\n";

    d_cmdsFile = "";
    d_hostsFile = "";
    d_logFile = "";

    while(1) 
    {
	int option_index;
	int c = getopt_long(argc, argv, "c:h:l:", long_options, &option_index);

	switch(c)
	{	    
	case 'c': d_cmdsFile = optarg; break;
	case 'h': d_hostsFile = optarg; break;
	case 'l': d_logFile = optarg; break;

	case -1:
	    // ran out of args, make sure we have everything...
	    if (d_cmdsFile == "" || d_hostsFile == "" || d_logFile == "")
	    {
		cerr << help << endl;
		exit(1);
	    }
	    return;
	    
	default: // unknown arg or error
	    cerr << help << endl;
	    exit(1);
	}
    }
}
