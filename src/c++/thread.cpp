#include <iostream>
#include <thread>

using namespace std;

void threadFunction(){
  cout << "Hello from the thread\n";
}

int main(){

  thread th(&threadFunction);
  cout << "Hello world\n";
  th.join();
  return 0;
}
