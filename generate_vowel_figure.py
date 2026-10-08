"""Original interval plot from aggregate JSON; all ambiguous references included.

No raw archive is read. Outputs are original PDF, PNG, JPG, EPS, SVG and CSV.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import csv
import json
import os


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results',type=Path,required=True,help='Reviewed raw_hz results.json')
    ap.add_argument('--output-dir',type=Path,required=True,help='New directory for figure exports')
    ap.add_argument('--anonymous',action='store_true',help='Leave figure author metadata neutral')
    args=ap.parse_args()
    assert __debug__, 'Run without -O'
    out=args.output_dir.resolve()
    assert not out.exists(), 'Choose a new output directory'
    out.mkdir(parents=True)
    os.environ.setdefault('MPLCONFIGDIR',str(out/'cache'))
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    DATA=json.loads(args.results.read_text())
    assert DATA['representation'] == 'raw_hz'
    WORDS = dict(zip(['iy','ih','ei','eh','ae','ah','aw','oa','oo','uw','uh','er'],
                     ['heed','hid','hayed','head','had','hod','hawed','hoed','hood',"who'd",'hud','heard']))
    PANELS = [(g,n) for g,x in DATA['groups'].items() for n in x['nearest'] if not n['guaranteed_unique']]
    assert len(PANELS) == 9
    plt.rcParams.update({'font.family':'DejaVu Serif','font.size':9,'axes.titlesize':10,
                         'pdf.fonttype':42,'ps.fonttype':42,'svg.fonttype':'none'})
    fig, axes = plt.subplots(3,3,figsize=(7.5,5.5))
    values = []
    for ax,(group,nearest) in zip(axes.ravel(),PANELS):
        ref = nearest['reference']
        for row,target in enumerate(nearest['possible_unique']):
            d = DATA['groups'][group]['distances'][ref][target]
            lo,hi,full = [d[k]/1000 for k in ('lower','upper','full')]
            ax.plot([lo,hi],[row,row],color='#555555',lw=1.1,marker='|',markersize=8)
            ax.plot(full,row,'o',color='black',markersize=4)
            values.append({'group':group,'reference':ref,'target':target,'lower_Hz2':d['lower'],
                           'upper_Hz2':d['upper'],'retained_Hz2':d['full'],
                           'retained_nearest':target==nearest['full']})
        ax.set_yticks(range(len(nearest['possible_unique'])),[WORDS[t] for t in nearest['possible_unique']])
        ax.set_ylim(-.55,len(nearest['possible_unique'])-.45)
        ax.invert_yaxis()
        ax.set_title(group.capitalize()+': '+WORDS[ref],loc='left',pad=8)
        ax.spines[['top','right','left']].set_visible(False)
        ax.tick_params(axis='y',length=0)
        ax.grid(axis='x',color='#dddddd',lw=.5)
        ax.set_axisbelow(True)
        ax.locator_params(axis='x',nbins=4)
    fig.supxlabel('Squared Gaussian-moment distance (1,000 Hz²)',fontsize=10,y=.065)
    fig.legend(handles=[Line2D([0],[0],color='#555555',marker='|',lw=1.1,label='Compatible interval'),
                        Line2D([0],[0],marker='o',color='black',lw=0,markersize=4,label='Retained covariance')],
               loc='lower center',ncol=2,frameon=False,bbox_to_anchor=(.5,-.007))
    fig.subplots_adjust(left=.075,right=.99,bottom=.18,top=.945,hspace=.73,wspace=.54)
    stem=out/'vowel_intervals'
    author='' if args.anonymous else 'Alexandre Menezes Barroso'
    fig.savefig(stem.with_suffix('.pdf'),metadata={'Author':author,'Title':'Compatible nearest-category distance intervals','Subject':'','Keywords':''})
    fig.savefig(stem.with_suffix('.png'),dpi=900,metadata={'Author':author})
    from PIL import Image
    jpeg_options={'quality':95}
    if author:
        exif=Image.Exif();exif[315]=author
        jpeg_options['exif']=exif.tobytes()
    fig.savefig(stem.with_suffix('.jpg'),dpi=900,pil_kwargs=jpeg_options)
    fig.savefig(stem.with_suffix('.svg'),metadata={'Creator':author,'Title':'Compatible nearest-category distance intervals'})
    fig.savefig(stem.with_suffix('.eps'),metadata={'Creator':'Matplotlib'})
    with stem.with_suffix('.csv').open('w') as f:
        writer=csv.DictWriter(f,fieldnames=list(values[0]));writer.writeheader();writer.writerows(values)
    plt.close(fig)
    exports={p.name:{'sha256':sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
             for p in sorted(out.glob('vowel_intervals.*'))}
    report={'status':'CREATED_FOR_VISUAL_REVIEW','panels':len(PANELS),'intervals':len(values),
            'results_sha256':sha256(args.results.read_bytes()).hexdigest(),
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'matplotlib':matplotlib.__version__,'raster_dpi':900,'figure_inches':[7.5,5.5],
            'anonymous_metadata':args.anonymous,'exports':exports,
            'limits':['Plotting success does not establish visual production quality.',
                      'Completion intervals are not sampling uncertainty or perceptual confusion.']}
    (out/'figure_exports.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
