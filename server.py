import os
from pathlib import Path

import pandas as pd

from src.dcr_to_petri_readable import Dcr2PetriTransport
from pm4py.objects.dcr.importer import importer as dcr_importer
from pm4py.objects.petri_net.importer import importer as pnml_importer

from concurrent.futures import ThreadPoolExecutor,wait

def run_analysis_on_pnmls(datasets_folder):

    pnml_res = []

    for root, dirs, files in os.walk(datasets_folder):
        for file in files:
            if file.endswith(".dcrxml"):
                pnml_res.append(os.path.join(root, file))

    analysis_results = {}
    for pnml in pnml_res:
        path_without_extension = os.path.splitext(pnml)[0]
        name_with_extension = os.path.basename(pnml)
        name = Path(pnml).stem
        version = name.split('_')[-1]
        # analysis
        tapn = pnml_importer.apply(pnml)
        analysis_results[name] = {}
        analysis_results[name]['version'] = version
        analysis_results[name]['#places'] = len(tapn.places)
        analysis_results[name]['#transitions'] = len(tapn.transitions)
        analysis_results[name]['#arcs'] = len(tapn.arcs)
    df = pd.DataFrame(analysis_results).T
    df.to_csv('models/analysis/optimization_analysis.csv')

def run_dcrxml_files(folder_with_dcr_xmls,override=False):
    dcrxml_res = []

    for root, dirs, files in os.walk(folder_with_dcr_xmls):
        for file in files:
            if file.endswith(".dcrxml"):
                dcrxml_res.append(os.path.join(root, file))
    dcrxml_res2 = []
    for dcrxml in dcrxml_res:
        if dcrxml.count('/')>4:
            dcrxml_res2.append(dcrxml)

    with ThreadPoolExecutor(16) as tpe:
            # futures = [tpe.submit(print, dcrxml) for dcrxml in dcrxml_res]
            futures = [tpe.submit(run_one_dcrxml_all_optimizations_file, dcrxml,override,2*60) for dcrxml in dcrxml_res]
    # with ThreadPoolExecutor(16) as tpe:
    #         # futures = [tpe.submit(print, dcrxml) for dcrxml in dcrxml_res]
    #         futures = [tpe.submit(run_one_dcrxml_all_optimizations_file, dcrxml,override,2*60) for dcrxml in dcrxml_res2]
    #         # for future in futures:
    #             # res = future.result(timeout=10*60)
    #             # print(f'[i] res: {res}')
    # exceptions = ['/home/vco/Datasets/12688511/CoSeLoG WABO 2.dcrxml',
    #               '/home/vco/Datasets/12681647/XES-files/event_log_choice_2_10000.dcrxml',
    #               '/home/vco/Datasets/12681647/XES-files/event_log_sequence_100_10000.dcrxml'
    #               ]
    # for dcrxml in dcrxml_res2:
    #     if dcrxml not in exceptions:
    #         run_one_dcrxml_all_optimizations_file(dcrxml, False, 2*60)


def run_one_dcrxml_all_optimizations_file(input_dcrxml_path, override=False, reachability_timeout=None):
    '''

    :param input_dcrxml_path: full path with extension
    :param reachability_timeout: timeout in seconds to search the reachability graph.
    :return:
    '''
    path_without_extension = os.path.splitext(input_dcrxml_path)[0]
    name_with_extension = os.path.basename(input_dcrxml_path)
    name = Path(input_dcrxml_path).stem

    dcrxml_files = [
        [input_dcrxml_path, f'{path_without_extension}_unoptimized.pnml', False, False, True,'unoptimized'],
        [input_dcrxml_path, f'{path_without_extension}_dcranalysis.pnml', True, False, False,'dcranalysis'],
        [input_dcrxml_path, f'{path_without_extension}_pnreachability.pnml', False, True, False,'pnreachability'],
        [input_dcrxml_path, f'{path_without_extension}_fulloptimization.pnml', True, True, False,'fulloptimization'],
    ]
    for mapping_call in dcrxml_files:
        if os.path.isfile(mapping_call[1]) and not override:
            print(f'[i] File {Path(mapping_call[1]).stem} already exists.')
            pass
        else:
            d2p = Dcr2PetriTransport(preoptimize=mapping_call[2], postoptimize=mapping_call[3],
                                     map_unexecutable_events=mapping_call[4],debug=False)
            d2p.print_steps = True
            d2p.reachability_timeout = 60*10 #10 minutes
            if reachability_timeout:
                d2p.reachability_timeout = reachability_timeout
            print(f'[i] Import {mapping_call[0]}')
            dcr = dcr_importer.apply(mapping_call[0])
            print(f'[i] Converting {mapping_call[0]} as {mapping_call[5]}')
            tapn, m = d2p.dcr2tapn(dcr, tapn_path=mapping_call[1])
            print(f'[i] Done for: {mapping_call[0]}!')

if __name__ == '__main__':
    # run_one_dcrxml_all_optimizations_file('/home/vco/Datasets/Hospital_log.dcrxml')
    # run_one_dcrxml_all_optimizations_file('/home/vco/Datasets/12683249/Road_Traffic_Fine_Management_Process.dcrxml',override=True)
    #run_one_dcrxml_all_optimizations_file('/home/vco/Projects/dcr-to-tapn/models/results/Road_Traffic_Fine_Management_Process.dcrxml', override=True)
    # run_one_dcrxml_all_optimizations_file('/home/vco/Projects/dcr-to-tapn/models/debug/Road_Traffic_Fine_Management_Process_test.dcrxml', override=True)
    # run_dcrxml_files('/home/vco/Datasets/')

    run_dcrxml_files('models/results/',override=True)
    print('[i] Done!')
