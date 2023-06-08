#Load packages
library(data.table)
library(purrr)
library(stringr)
library(SuperLearner)
library(gam)
library(glmnet)
library(polspline)
library(randomForest)
library(kernlab)
library(KernelKnn)
library(ranger)
library(biglasso)
library(xgboost)
library(caret)
library(nnet)
library(gbm)
library(arm)
library(earth)
library(lubridate)
library(skimr)
library(qs)
library(ROCR)
library(scattermore)
library(here)
library(hrbrthemes)
library(fst)
library(dplyr)


##############################################################################
## This function calculates the effort-benefit curve discussed in the paper ##
##############################################################################
eb.calc <- function(dt,wind_days=90,cutoff=1,short=FALSE) {
  if (short==TRUE) {
    nloop=1001
    ndenom=1000
  } else {
    nloop=10001
    ndenom=10000/max(dt[,p_combined])
  }
  eb<-matrix(0,nrow=nloop,ncol=18)
  for (i in 1:nloop) {
    #would this patient surpass threshold (i-1)/ndenom at this consultation?
    dt[, thresh:=(p_combined>=(i-1)/ndenom)]

    #what proportion of consultations in children without T1D result in an alert (false positive) under this threshold?
    prop_bg_nonT1<-dt[,sum(thresh*(1-T1D))/sum(1-T1D)]
    if (prop_bg_nonT1<0.00001) {
      break
    }
    se_prop_bg_nonT1<-dt[,sqrt(((sum(thresh*(1-T1D))/sum(1-T1D))*(1-(sum(thresh*(1-T1D))/sum(1-T1D))))/(sum(1-T1D)))]

    #is a T1D "caught" (i.e. alerted during the run-up to diagnosis) at this consultation by this threshold? Yes (we assume) if they surpass it, and will be diagnosed within wind_days days...
    dt[, caught:=ifelse(thresh=="TRUE" & T1D==1 & days_from_T1D<=wind_days,1,0)]

    #for those who are caught, by how many days is their diagnosis anticipated?
    dt[, days_ant:=ifelse(thresh=="TRUE" & T1D==1 & days_from_T1D<=wind_days,days_from_T1D,0)]

    #is there an opportunity to catch T1D at this consultation? Yes (we assume) if the patient is an eventual T1D and will be diagnosed within wind_days days...
    dt[, opportunity:=ifelse(T1D==1 & days_from_T1D<=wind_days,1,0)]

    #is this patient a T1D who is identified at some point?
    dt[, caught_overall:=max(caught),by=ALF_PE]

    #by how many days is their diagnosis anticipated?
    dt[, max_days_ant:=max(days_ant),by=ALF_PE]

    #is this patient a T1D with an opportunity to be caught at some point?
    dt[, opp_overall:=max(opportunity),by=ALF_PE]

    #what proportion of T1Ds have an opportunity to be caught?
    prop_T1D_opp=nrow(dt[EVENT_SEQN==1 & opp_overall==1])/nrow(dt[EVENT_SEQN==1 & T1D==1])

    #define the sensitivity of the algorithm as the proportion of T1Ds who are caught
    sens<-dt[EVENT_SEQN==1][, sum(caught_overall)/sum(T1D)]
    se_sens<-dt[EVENT_SEQN==1][, sqrt(((sum(caught_overall)/sum(T1D))*(1-(sum(caught_overall)/sum(T1D))))/(sum(T1D)))]

    #calculate the mean number of days by which diagnosis is anticipated at each threshold for those who are caught
    mean_anticipation<-mean(dt[EVENT_SEQN==1 & caught_overall==1][,max_days_ant],na.rm=TRUE)
    n_anticipation<-sum(dt[EVENT_SEQN==1 & caught_overall==1][,EVENT_SEQN],na.rm=TRUE)
    se_mean_anticipation<-sd(dt[EVENT_SEQN==1 & caught_overall==1][,max_days_ant],na.rm=TRUE)/(sqrt(n_anticipation))

    #calculate the median and (first,third) quartiles of the number of days by which diagnosis is anticipated at each threshold for those who are caught
    quartiles_anticipation<-quantile(dt[EVENT_SEQN==1 & caught_overall==1][,max_days_ant],probs=c(0.25,0.5,0.75),na.rm=TRUE)
    se_75c_anticipation<-sqrt(75*25)/(100*sqrt(n_anticipation)*(dnorm(quartiles_anticipation[3],mean_anticipation,sd(dt[EVENT_SEQN==1 & caught_overall==1][,max_days_ant],na.rm=TRUE))))


    #calculate the proportion of T1Ds for which diagnosis is anticipated by at least x days at each threshold for those who are caught, x=1,2,...,7
    prop_antic_g1d<-mean(dt[EVENT_SEQN==1 & caught_overall==1][,as.numeric(max_days_ant>=1)],na.rm=TRUE)
    prop_antic_g2d<-mean(dt[EVENT_SEQN==1 & caught_overall==1][,as.numeric(max_days_ant>=2)],na.rm=TRUE)
    prop_antic_g3d<-mean(dt[EVENT_SEQN==1 & caught_overall==1][,as.numeric(max_days_ant>=3)],na.rm=TRUE)
    prop_antic_g4d<-mean(dt[EVENT_SEQN==1 & caught_overall==1][,as.numeric(max_days_ant>=4)],na.rm=TRUE)
    prop_antic_g5d<-mean(dt[EVENT_SEQN==1 & caught_overall==1][,as.numeric(max_days_ant>=5)],na.rm=TRUE)
    prop_antic_g6d<-mean(dt[EVENT_SEQN==1 & caught_overall==1][,as.numeric(max_days_ant>=6)],na.rm=TRUE)
    prop_antic_g7d<-mean(dt[EVENT_SEQN==1 & caught_overall==1][,as.numeric(max_days_ant>=7)],na.rm=TRUE)


    #calculate the ppv at this threshold
    ppv<-sens*prev/(sens*prev+(1-prev)*(prop_bg_nonT1))

    #calculate 1 minus the npv at this threshold
    om_npv<-prev*(1-sens)/(1-prop_bg_nonT1*(1-prev)-sens*prev)

    #put all this into an effort-benefit matrix
    eb[i,1]<-prop_bg_nonT1*(1-prev)+sens*prev
    eb[i,2]<-sens
    eb[i,3]<-(i-1)/1000
    eb[i,4]<-quartiles_anticipation[2]
    eb[i,5]<-quartiles_anticipation[1]
    eb[i,6]<-quartiles_anticipation[3]
    eb[i,7]<-mean_anticipation
    eb[i,8]<-ppv
    eb[i,9]<-prop_antic_g1d
    eb[i,10]<-prop_antic_g2d
    eb[i,11]<-prop_antic_g3d
    eb[i,12]<-prop_antic_g4d
    eb[i,13]<-prop_antic_g5d
    eb[i,14]<-prop_antic_g6d
    eb[i,15]<-prop_antic_g7d
    eb[i,16]<-se_75c_anticipation
    eb[i,17]<-se_mean_anticipation
    eb[i,18]<-se_sens
  }    
  eb<-eb[eb[,1]<=cutoff,]
  
  #calculate the area under the eb curve
  aucm<-matrix(0,as.numeric(nrow(eb)),5)
  aucm[,1]<-eb[,1]
  aucm[,3]<-eb[,2]
  aucm[,2]<-shift(eb[,1],n=1,fill=1,type="lag")
  aucm[,4]<-shift(eb[,2],n=1,fill=1,type="lag")
  aucm[,5]<-(aucm[,2]-aucm[,1])*0.5*(aucm[,4]-aucm[,3])+(aucm[,2]-aucm[,1])*aucm[,3]
  aucm[1,5]<-0
  auc<-sum(aucm[,5])
  eblist<-list(eb,auc,prop_T1D_opp,aucm)
  return(eblist)
}


################################################################################################################
## At this point, four datasets are read: patient_new_id, patient_flagged, consultation_types and hes_patiemt ##
################################################################################################################


#######################################################################
## The next chunk of code merges the primary and secondary care data ##
#######################################################################
#create lookup
gen_hesid_to_patid_lkup <- hes_patient[patient_new_id[.id == "hes",.(gen_hesid = as.integer(new_id))], on = c("gen_hesid"), mult = "all"] #e.g. [gen_hesid == 57,.(gen_hesid, patid)]

#get original ids
regexp <- "[[:digit:]]+"
patient_new_id[.id == "gp_only",orig_patid := as.numeric(str_extract(new_id, regexp))]
patient_new_id[.id == "hes",orig_gen_hesid :=as.numeric(new_id)]
patient_new_id[,new_id2 := ifelse(.id == "hes",orig_gen_hesid, orig_patid + max(orig_patid,na.rm = TRUE))] # making sure new_id2 never == to an original patid by adding largest patid to every original patid

# Link patients who have no HES data
patient_flagged[patient_new_id[, .(
  orig_patid,
  .id,
  gender,
  yob,
  mob,
  imp_birth_date,
  birthday_15,
  Start,
  End,
  first_T1D_HES_in_fup,
  first_T1D_med_in_fup,
  first_T1D_prod_in_fup,
  first_DKA_HES_in_fup,
  t1d_diag_dt,
  admimeth_grp,
  deathdate,
  orig_gen_hesid,
  new_id2
)], on = c("patid" = "orig_patid"), nomatch = NULL] -> merged_gp_only

# Link patients who have HES data - need to use gen_hesid_to_patid_lkup too
patient_flagged[gen_hesid_to_patid_lkup[
  ,.(patid, gen_hesid)][patient_new_id[, .(
    orig_gen_hesid,
    .id,
    gender,
    yob,
    mob,
    imp_birth_date,
    birthday_15,
    Start,
    End,
    first_T1D_HES_in_fup,
    first_T1D_med_in_fup,
    first_T1D_prod_in_fup,
    first_DKA_HES_in_fup,
    t1d_diag_dt,
    admimeth_grp,
    deathdate,
    orig_gen_hesid,
    new_id2
  )], on = c("gen_hesid"= "orig_gen_hesid"), nomatch = NULL], on = "patid", nomatch = NULL] -> merged_hes 

# Same but for consultation_types
consultation_types[patient_new_id[, .(
  orig_patid,
  .id,
  gender,
  yob,
  mob,
  imp_birth_date,
  birthday_15,
  Start,
  End,
  first_T1D_HES_in_fup,
  first_T1D_med_in_fup,
  first_T1D_prod_in_fup,
  first_DKA_HES_in_fup,
  t1d_diag_dt,
  admimeth_grp,
  deathdate,
  orig_gen_hesid,
  new_id2
)], on = c("patid" = "orig_patid"), nomatch = NULL] -> consultations_gp_only

consultation_types[gen_hesid_to_patid_lkup[#gen_hesid == 57
  ,.(patid, gen_hesid)][patient_new_id[, .(
    orig_gen_hesid,
    .id,
    gender,
    yob,
    mob,
    imp_birth_date,
    birthday_15,
    Start,
    End,
    first_T1D_HES_in_fup,
    first_T1D_med_in_fup,
    first_T1D_prod_in_fup,
    first_DKA_HES_in_fup,
    t1d_diag_dt,
    admimeth_grp,
    deathdate,
    orig_gen_hesid,
    new_id2
  )], on = c("gen_hesid"= "orig_gen_hesid"), nomatch = NULL], on = "patid", nomatch = NULL] -> consultations_hes 

#merge gp and hes data - all consultations
merged_cprd_with_unpermitted <- rbindlist(list("gp_only" = merged_gp_only,"hes" = merged_hes), fill = TRUE, idcol = "file")
merged_cprd_with_unpermitted[,line_number:=seq.int(nrow(merged_cprd_with_unpermitted))]
merged_cprd_with_unpermitted[,unique_id:=new_id2*10000+as.numeric(eventdate)-10956]
merged_cprd_with_unpermitted[,duplicate:=as.numeric(duplicated(merged_cprd_with_unpermitted$unique_id))]

#select only consultations to be used in the analysis
merged_consultations <- rbindlist(list("gp_only" = consultations_gp_only,"hes" = consultations_hes), fill = TRUE, idcol = "file")
merged_consultations[,unique_id:=new_id2*10000+as.numeric(eventdate)-10956]
merged_consultations<-merged_consultations[,.SD,.SDcols="unique_id"]
merged_consultations[,duplicate:=as.numeric(duplicated(merged_consultations$unique_id))]
merged_consultations[,permitted:=1]
merged_consultations<-merged_consultations[duplicate==0]
merged_consultations[,duplicate:=NULL]

merged_cprd <- left_join(x = merged_cprd_with_unpermitted, y = merged_consultations, by="unique_id")
merged_cprd <- setnafill(merged_cprd, fill=0, cols=c("permitted"))
merged_cprd[,unique_id:=NULL]

setkey(merged_cprd,new_id2,eventdate)

rm(patient_flagged)
rm(patient_new_id)
rm(gen_hesid_to_patid_lkup)
rm(hes_patient)
rm(merged_gp_only)
rm(merged_hes)
rm(consultations_gp_only)
rm(consultations_hes)
rm(consultation_types)
rm(merged_cprd_with_unpermitted)
rm(merged_consultations)

#####################################################################################
## Renaming variables so that CPRD and SAIL match exactly (needed by SuperLearner) ##
#####################################################################################

setnames(merged_cprd,"Blurred vision","BLURRED_VISION")
setnames(merged_cprd,"Contact non specific","CONTACT_NON_SPEC")
setnames(merged_cprd,"Family history","FAMILY_HISTORY")
setnames(merged_cprd,"Lower RTI","LOWER_RTI")
setnames(merged_cprd,"Non-oral antibiotics","NON_ORAL_ABX")
setnames(merged_cprd,"Skin infections","SKIN_INFECTIONS")
setnames(merged_cprd,"Upper RTI","UPPER_RTI")
setnames(merged_cprd,"Weight loss","WEIGHT_LOSS")
setnames(merged_cprd,"gender","GNDR_CD")
setnames(merged_cprd,"Antipyretic","ANTIPYRETIC")
setnames(merged_cprd,"AtopicAllergy","ATOPICALLERGY")
setnames(merged_cprd,"Behaviour","BEHAVIOUR")
setnames(merged_cprd,"Bloods","BLOODS")
setnames(merged_cprd,"Breathlessness","BREATHLESSNESS")
setnames(merged_cprd,"Constipation","CONSTIPATION")
setnames(merged_cprd,"Fungal","FUNGAL")
setnames(merged_cprd,"Gastrointestinal","GASTROINTESTINAL")
setnames(merged_cprd,"Headache","HEADACHE")
setnames(merged_cprd,"Obesity","OBESITY")
setnames(merged_cprd,"Prednisolone","PREDNISOLONE")
setnames(merged_cprd,"Rash","RASH")
setnames(merged_cprd,"Thirst","THIRST")
setnames(merged_cprd,"Tiredness","TIREDNESS")
setnames(merged_cprd,"Urinary","URINARY")
setnames(merged_cprd,"Vomiting_nausea","VOMITING_NAUSEA")
setnames(merged_cprd,"Polyuria","POLYURIA")

####################################################################################################
## Define variables so that dataset can be restricted to correct inclusion and exclusion criteria ##
####################################################################################################
merged_cprd[,included1:=as.numeric(AGE_AT_EVT.x<15.00958)]               
merged_cprd[,included2:=as.numeric(is.na(t1d_diag_dt)==TRUE | eventdate<=t1d_diag_dt)]               
merged_cprd[,included3:=as.numeric(susp_t1d_no_conf_in_diag_date==FALSE | is.na(first_T1D_med_in_fup)==TRUE | eventdate<=first_T1D_med_in_fup)]
merged_cprd[,included4:=as.numeric(susp_t1d_no_conf_in_diag_date==FALSE | is.na(first_T1D_prod_in_fup)==TRUE | eventdate<=first_T1D_prod_in_fup)]
merged_cprd[,included5:=as.numeric(susp_t1d_no_conf_in_diag_date==FALSE | is.na(first_T1D_HES_in_fup)==TRUE | eventdate<=first_T1D_HES_in_fup)]               
merged_cprd<-merged_cprd[, check_timings:=eventdate<=t1d_diag_dt | is.na(t1d_diag_dt)]
merged_cprd<-merged_cprd[, check_timings_max:=max(check_timings),by=new_id2]


#############################################################
## Dervive some age and date variables that will be needed ##
#############################################################

merged_cprd[, "time_until_diagnosis" := time_length(interval(eventdate, t1d_diag_dt), "days")]
merged_cprd[, "AGE_AT_EVT.x" := as.numeric(eventdate - imp_birth_date) / 365.25]
merged_cprd[, "AGE_AT_EVT_days" := as.numeric(eventdate - imp_birth_date)]
merged_cprd[, "AGE_AT_T1D_DIAG" := as.numeric(t1d_diag_dt - imp_birth_date)/365.25]
merged_cprd[, "AGE_AT_T1D_DIAG_u6" := AGE_AT_T1D_DIAG<7]
merged_cprd[, "AGE_AT_T1D_DIAG_7t12" := AGE_AT_T1D_DIAG>=7 & AGE_AT_T1D_DIAG<13]
merged_cprd[, "AGE_AT_T1D_DIAG_13p" := AGE_AT_T1D_DIAG>=13]

merged_cprd[, "AGE_AT_FIRST_EVENT_days" := as.numeric(min(eventdate) - imp_birth_date), by =  new_id2]
merged_cprd[, "AGE_AT_FIRST_EVENT" := AGE_AT_FIRST_EVENT_days/365.25]
merged_cprd[, "AGE_AT_LAST_EVENT_days" := as.numeric(max(eventdate) - imp_birth_date), by =  new_id2]
merged_cprd[, "AGE_AT_LAST_EVENT" := AGE_AT_LAST_EVENT_days/365.25]

merged_cprd[, EVENT_SEQN := 1:.N, by = .(new_id2)]

merged_cprd[, "AVE_INT_LENGTH" := as.numeric(AGE_AT_EVT_days - AGE_AT_FIRST_EVENT_days) /
              EVENT_SEQN]               

merged_cprd[,"AGE_u7":=AGE_AT_EVT.x<7]               
merged_cprd[,"AGE_7t12":=AGE_AT_EVT.x>=7 & AGE_AT_EVT.x<13]               
merged_cprd[,"AGE_13p":=AGE_AT_EVT.x>=13]               

merged_cprd[, "AGE_AT_STUDY_START" := as.numeric(as.Date("2000-01-01") - imp_birth_date)/365.25, by =  new_id2]
merged_cprd[, "AGE_AT_STUDY_END" := as.numeric(as.Date("2016-12-31") - imp_birth_date)/365.25, by =  new_id2]
merged_cprd[,DOD:=deathdate]

merged_cprd[, "AGE_AT_DEATH" := as.numeric(DOD-imp_birth_date)/365.25]

merged_cprd<-as.data.table(mutate(as.data.frame(merged_cprd),AGE_AT_STUDY_EXIT1=pmin(AGE_AT_STUDY_END,AGE_AT_T1D_DIAG,na.rm=TRUE)))
merged_cprd<-as.data.table(mutate(as.data.frame(merged_cprd),AGE_AT_STUDY_EXIT2=pmin(AGE_AT_STUDY_EXIT1,AGE_AT_DEATH,na.rm=TRUE)))
merged_cprd<-as.data.table(mutate(as.data.frame(merged_cprd),AGE_AT_STUDY_EXIT=pmin(AGE_AT_STUDY_EXIT2,15.00958)))
merged_cprd[,AGE_AT_STUDY_EXIT1:=NULL]
merged_cprd[,AGE_AT_STUDY_EXIT2:=NULL]
merged_cprd<-as.data.table(mutate(as.data.frame(merged_cprd),DATE_STUDY_EXIT1=pmin(as.Date("2016-12-31"),t1d_diag_dt,na.rm=TRUE)))
merged_cprd<-as.data.table(mutate(as.data.frame(merged_cprd),DATE_STUDY_EXIT2=pmin(DATE_STUDY_EXIT1,DOD,na.rm=TRUE)))
merged_cprd<-as.data.table(mutate(as.data.frame(merged_cprd),DATE_STUDY_EXIT=pmin(DATE_STUDY_EXIT2,birthday_15)))
merged_cprd[, "AGE_AT_LAST_EVENT_days" := as.numeric(min(max(eventdate),DATE_STUDY_EXIT) - imp_birth_date), by =  new_id2]
merged_cprd[, "AGE_AT_LAST_EVENT" := AGE_AT_LAST_EVENT_days/365.25]

merged_cprd[,YEARS_CONTRIBUTED_TO_STUDY:=AGE_AT_LAST_EVENT-AGE_AT_FIRST_EVENT]

################################################################################################################################
## Some code to flag and describe those who may have T1D but we're not sufficiently sure of the date of diagnosis to use them ##
################################################################################################################################

merged_cprd<-merged_cprd[, suspected_t1d:=is.na(first_T1D_med_in_fup)==FALSE | is.na(first_T1D_HES_in_fup)==FALSE | is.na(first_T1D_prod_in_fup)==FALSE]
merged_cprd<-merged_cprd[, susp_t1d_no_conf_in_diag_date:=suspected_t1d==TRUE & is.na(t1d_diag_dt)==TRUE]

#how many "suspected T1Ds" are there?
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE][,EVENT_SEQN])
table(merged_cprd[susp_t1d_no_conf_in_diag_date==TRUE][,susp_t1d_no_conf_in_diag_date])

#Now look at all the reasons for being a `suspected T1D':

#Reason 1: no HES code (but PROD and MED)
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==TRUE &
                    is.na(first_T1D_prod_in_fup)==FALSE &
                    is.na(first_T1D_med_in_fup)==FALSE][,EVENT_SEQN])

#Reason 2: no PROD code (but HES and MED)
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==FALSE &
                    is.na(first_T1D_prod_in_fup)==TRUE &
                    is.na(first_T1D_med_in_fup)==FALSE][,EVENT_SEQN])

#Reason 3: no MED code (but HES and PROD)
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==FALSE &
                    is.na(first_T1D_prod_in_fup)==FALSE &
                    is.na(first_T1D_med_in_fup)==TRUE][,EVENT_SEQN])

#Reason 4: no HES or PROD code (but MED)
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==TRUE &
                    is.na(first_T1D_prod_in_fup)==TRUE &
                    is.na(first_T1D_med_in_fup)==FALSE][,EVENT_SEQN])

#Reason 5: no HES or MED code (but PROD)
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==TRUE &
                    is.na(first_T1D_prod_in_fup)==FALSE &
                    is.na(first_T1D_med_in_fup)==TRUE][,EVENT_SEQN])

#Reason 6: no PROD or MED code (but HES)
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==FALSE &
                    is.na(first_T1D_prod_in_fup)==TRUE &
                    is.na(first_T1D_med_in_fup)==TRUE][,EVENT_SEQN])

#Reason 7: all three codes there but PROD and MED before HES
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==FALSE &
                    is.na(first_T1D_prod_in_fup)==FALSE &
                    is.na(first_T1D_med_in_fup)==FALSE & 
                    first_T1D_prod_in_fup-first_T1D_HES_in_fup<0  & 
                    first_T1D_med_in_fup-first_T1D_HES_in_fup<0][,EVENT_SEQN])

#Reason 8: all three codes there but PROD before HES (and MED OK, ie >=HES-1)
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==FALSE &
                    is.na(first_T1D_prod_in_fup)==FALSE &
                    is.na(first_T1D_med_in_fup)==FALSE & 
                    first_T1D_prod_in_fup-first_T1D_HES_in_fup<0 & 
                    first_T1D_med_in_fup-first_T1D_HES_in_fup>=-1][,EVENT_SEQN])

#Reason 9: all three codes there but MED before HES (and PROD OK)
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==TRUE &
                    is.na(first_T1D_HES_in_fup)==FALSE &
                    is.na(first_T1D_prod_in_fup)==FALSE &
                    is.na(first_T1D_med_in_fup)==FALSE & 
                    first_T1D_prod_in_fup-first_T1D_HES_in_fup>=0 & 
                    first_T1D_med_in_fup-first_T1D_HES_in_fup+1<0][,EVENT_SEQN])



merged_cprd[, table(eventdate<=t1d_diag_dt | is.na(t1d_diag_dt))]
merged_cprd[EVENT_SEQN==1][, table(suspected_t1d)]
merged_cprd[EVENT_SEQN==1][, table(susp_t1d_no_conf_in_diag_date)]


########################################
## More code for descriptive analyses ##
########################################

#Make a flag for diagnosis in DKA
merged_cprd[, "diagnosis_in_DKA" := fifelse(is.na(first_DKA_HES_in_fup)==FALSE & is.na(t1d_diag_dt)==FALSE,as.numeric(first_DKA_HES_in_fup-t1d_diag_dt<=1),0)]
merged_cprd[EVENT_SEQN==1][, table(diagnosis_in_DKA)]

#how many alive at study start
table(merged_cprd[EVENT_SEQN==1][,AGE_AT_STUDY_START]<0)
#how many GP contacts do they contribute in total
table(merged_cprd[,AGE_AT_STUDY_START]<0)
#at what rate?
#PERSON-TIME:
sum(merged_cprd[EVENT_SEQN==1 & AGE_AT_STUDY_START>=0][,YEARS_CONTRIBUTED_TO_STUDY])
sum(merged_cprd[EVENT_SEQN==1 & AGE_AT_STUDY_START<0][,YEARS_CONTRIBUTED_TO_STUDY])

#how many suspected T1D but without clear date of diagnosis
table(merged_cprd[EVENT_SEQN==1][,susp_t1d_no_conf_in_diag_date]==TRUE)
#how many contacts do they contribute in total
table(merged_cprd[,susp_t1d_no_conf_in_diag_date]==TRUE)

#how many develop T1D with reliable date at diagnosis and <15 at diagnosis
table(merged_cprd[EVENT_SEQN==1 & is.na(t1d_diag_dt)==FALSE][,AGE_AT_T1D_DIAG]<15.0098)
#how many contacts do they contribute in total
table(merged_cprd[,is.na(t1d_diag_dt) & AGE_AT_T1D_DIAG<15.0098]==FALSE)
#at what rate?
#PERSON-TIME:
sum(merged_cprd[EVENT_SEQN==1 & is.na(t1d_diag_dt)==FALSE][,YEARS_CONTRIBUTED_TO_STUDY])


#age distn at date at diagnosis
table(merged_cprd[EVENT_SEQN==1 & is.na(t1d_diag_dt)==FALSE & AGE_AT_T1D_DIAG<15.0098][,AGE_AT_T1D_DIAG]<7)
table(merged_cprd[EVENT_SEQN==1 & is.na(t1d_diag_dt)==FALSE & AGE_AT_T1D_DIAG<15.0098][,AGE_AT_T1D_DIAG]<13)
quantile(merged_cprd[EVENT_SEQN==1 & is.na(t1d_diag_dt)==FALSE & AGE_AT_T1D_DIAG<15.0098][,AGE_AT_T1D_DIAG],p=c(0.25,0.5,0.75))

#how many would be censored due to turning 15 before study end if they lived to 15
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & (is.na(t1d_diag_dt)==TRUE | (is.na(t1d_diag_dt)==FALSE & AGE_AT_T1D_DIAG>=15.0098) | (is.na(t1d_diag_dt)==FALSE & t1d_diag_dt>as.Date("2016-12-31")))][,AGE_AT_STUDY_END]>=15.0098)
#how many die <15 and before T1D diagnosis during study?
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & (is.na(t1d_diag_dt)==TRUE | (is.na(t1d_diag_dt)==FALSE & AGE_AT_T1D_DIAG>=15.0098) | (is.na(t1d_diag_dt)==FALSE & t1d_diag_dt>as.Date("2016-12-31"))) & (is.na(DOD)==TRUE | AGE_AT_DEATH<15.0098)][,DOD<=as.Date("2016-12-31")])
#how many censored at study end
table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & (is.na(t1d_diag_dt)==TRUE | (is.na(t1d_diag_dt)==FALSE & AGE_AT_T1D_DIAG>=15.0098) | (is.na(t1d_diag_dt)==FALSE & t1d_diag_dt>as.Date("2016-12-31"))) & (is.na(DOD)==TRUE | (is.na(DOD)==FALSE & DOD>as.Date("2016-12-31")) | (is.na(DOD)==FALSE & AGE_AT_DEATH>15.0098))][,AGE_AT_STUDY_END]<15.0098)

merged_cprd_permitted<-merged_cprd[check_timings==TRUE & permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1]
merged_cprd_permitted[, EVENT_SEQN := 1:.N, by = .(new_id2)]

table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE][,EVENT_SEQN])
table(is.na(merged_cprd[susp_t1d_no_conf_in_diag_date==FALSE][,EVENT_SEQN])==FALSE)

table(merged_cprd_permitted[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE][,EVENT_SEQN])
table(is.na(merged_cprd_permitted[susp_t1d_no_conf_in_diag_date==FALSE][,EVENT_SEQN])==FALSE)

merged_cprd[,nont1:=(is.na(t1d_diag_dt)==TRUE | (is.na(t1d_diag_dt)==FALSE & AGE_AT_T1D_DIAG>=15.0098) | (is.na(t1d_diag_dt)==FALSE & t1d_diag_dt>as.Date("2016-12-31")))]
merged_cprd_permitted[,nont1:=(is.na(t1d_diag_dt)==TRUE | (is.na(t1d_diag_dt)==FALSE & AGE_AT_T1D_DIAG>=15.0098) | (is.na(t1d_diag_dt)==FALSE & t1d_diag_dt>as.Date("2016-12-31")))]

table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE][,nont1])
table(merged_cprd[susp_t1d_no_conf_in_diag_date==FALSE][,nont1])

table(merged_cprd_permitted[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE][,nont1])
table(merged_cprd_permitted[susp_t1d_no_conf_in_diag_date==FALSE][,nont1])

##############################################################
## More data management - defining lagged consultations etc ##
##############################################################
setnames(merged_cprd,"eventdate","EVENT_DT")

flag_names<-c('ANTIPYRETIC','ATOPICALLERGY','BEHAVIOUR','BLOODS','BLURRED_VISION','BREATHLESSNESS','CONSTIPATION','CONTACT_NON_SPEC','FAMILY_HISTORY','FUNGAL','GASTROINTESTINAL','HEADACHE','LOWER_RTI','NON_ORAL_ABX','OBESITY','PREDNISOLONE','RASH','SKIN_INFECTIONS','THIRST','TIREDNESS','UPPER_RTI','URINARY','VOMITING_NAUSEA','WEIGHT_LOSS','ANTIBIOTICS','POLYURIA','AGE_AT_EVT.x','AVE_INT_LENGTH','EVENT_DT')

lagged_names<-paste("lagged_",flag_names,sep="_")
lagged_names_2<-paste("lagged_2_",flag_names,sep="_")

merged_cprd<-merged_cprd[,(lagged_names):=shift(.SD,1,0,"lag"),.SDcols=flag_names,by=new_id2]

merged_cprd<-merged_cprd[,event_interval:=as.integer((EVENT_DT-lagged__EVENT_DT)*(lagged__EVENT_DT>0))]

merged_cprd<-merged_cprd[,event_interval_diff:=ifelse(event_interval>0 & lagged__AVE_INT_LENGTH>0,as.numeric((event_interval-lagged__AVE_INT_LENGTH)),0)]

merged_cprd<-merged_cprd[,event_interval_ratio:=ifelse(event_interval>0 & lagged__AVE_INT_LENGTH>0,log(as.numeric(event_interval)/as.numeric(lagged__AVE_INT_LENGTH)),0)]

merged_cprd<-merged_cprd[,(lagged_names_2):=shift(.SD,2,0,"lag"),.SDcols=flag_names,by=new_id2]

merged_cprd<-merged_cprd[,event_interval_2:=as.integer((lagged__EVENT_DT-lagged_2__EVENT_DT)*(lagged_2__EVENT_DT>0))]

merged_cprd<-merged_cprd[,event_interval_diff_2:=ifelse(event_interval_2>0 & lagged_2__AVE_INT_LENGTH>0,as.numeric((event_interval_2-lagged_2__AVE_INT_LENGTH)),0)]

merged_cprd<-merged_cprd[,event_interval_ratio_2:=ifelse(event_interval_2>0 & lagged_2__AVE_INT_LENGTH>0,log(as.numeric(event_interval_2)/as.numeric(lagged_2__AVE_INT_LENGTH)),0)]

flag_names<-c('ANTIPYRETIC','ATOPICALLERGY','BEHAVIOUR','BLOODS','BLURRED_VISION','BREATHLESSNESS','CONSTIPATION','CONTACT_NON_SPEC','FAMILY_HISTORY','FUNGAL','GASTROINTESTINAL','HEADACHE','LOWER_RTI','NON_ORAL_ABX','OBESITY','PREDNISOLONE','RASH','SKIN_INFECTIONS','THIRST','TIREDNESS','UPPER_RTI','URINARY','VOMITING_NAUSEA','WEIGHT_LOSS','ANTIBIOTICS','POLYURIA','AGE_AT_EVT.x','AVE_INT_LENGTH')

merged_cprd[,c('lagged__EVENT_DT','lagged_2__EVENT_DT'):=NULL]    

merged_cprd[,AGE_AT_FIRST_EVENT_days:=NULL]

merged_cprd[,t1d:=is.na(t1d_diag_dt)==FALSE]
merged_cprd[,fourT:=THIRST+WEIGHT_LOSS+POLYURIA+TIREDNESS]


#########################################################################
## Predictions from logistic regression (for later comparison with SL) ##
#########################################################################

merged_cprd[,glm.lp1d:=-5.655+0.1086*AGE_AT_EVT.x+0.04114*GNDR_CD-0.8359*ANTIPYRETIC-2.403*ATOPICALLERGY-14.12*BEHAVIOUR+2.141*BLOODS-13.73*BLURRED_VISION+2.186*BREATHLESSNESS-1.65*CONSTIPATION+0.795*CONTACT_NON_SPEC-1.928*FAMILY_HISTORY+0.2888*FUNGAL-0.308*GASTROINTESTINAL-1.821*HEADACHE-2.209*LOWER_RTI-1.64*NON_ORAL_ABX-13.84*OBESITY-0.7166*PREDNISOLONE-1.407*RASH-1.693*SKIN_INFECTIONS+6.591*THIRST+2.079*TIREDNESS-1.254*UPPER_RTI+1.608*URINARY+3.956*POLYURIA+1.732*VOMITING_NAUSEA+1.436*WEIGHT_LOSS+0.001828*AVE_INT_LENGTH+0.7273*AGE_u7+0.9149*AGE_7t12-1.755*ANTIBIOTICS+0.001107*event_interval_2-0.0004088*event_interval_diff_2+0.004208*event_interval_ratio_2+0.00128*event_interval+0.0005734*event_interval_diff-0.2187*event_interval_ratio]
merged_cprd[,glm.lp7d:=-6.242+0.1079*AGE_AT_EVT.x+0.04474*GNDR_CD+0.1203*ANTIPYRETIC-0.7663*ATOPICALLERGY-13.09*BEHAVIOUR+2.127*BLOODS-13.48*BLURRED_VISION+0.2029*BREATHLESSNESS+0.03814*CONSTIPATION+0.6962*CONTACT_NON_SPEC-14.65*FAMILY_HISTORY+1.527*FUNGAL+0.0126*GASTROINTESTINAL+0.4054*HEADACHE-1.333*LOWER_RTI-1.185*NON_ORAL_ABX+0.2876*OBESITY-13.03*PREDNISOLONE-0.3344*RASH-0.6229*SKIN_INFECTIONS+6.235*THIRST+2.186*TIREDNESS+0.009764*UPPER_RTI+0.8175*URINARY+3.078*POLYURIA+1.688*VOMITING_NAUSEA+1.623*WEIGHT_LOSS-0.0001657*AVE_INT_LENGTH+0.7273*AGE_u7+0.6772*AGE_7t12-0.2028*ANTIBIOTICS+0.002139*event_interval_2-0.0011480*event_interval_diff_2-0.08556*event_interval_ratio_2+0.00121*event_interval+0.0005512*event_interval_diff-0.23*event_interval_ratio]
merged_cprd[,glm.lp14d:=-7.389+0.1533*AGE_AT_EVT.x+0.1795*GNDR_CD-0.1455*ANTIPYRETIC-0.1023*ATOPICALLERGY-12.61*BEHAVIOUR+1.124*BLOODS-0.1122*BLURRED_VISION-12.15*BREATHLESSNESS-1.156*CONSTIPATION-0.7375*CONTACT_NON_SPEC-11.84*FAMILY_HISTORY+1.218*FUNGAL-0.04819*GASTROINTESTINAL+0.5151*HEADACHE-0.7428*LOWER_RTI-0.1748*NON_ORAL_ABX+1.883*OBESITY-12.22*PREDNISOLONE-0.3704*RASH+0.08027*SKIN_INFECTIONS+4.743*THIRST+2.317*TIREDNESS+0.07603*UPPER_RTI+0.7537*URINARY+1.753*POLYURIA+0.6558*VOMITING_NAUSEA+0.3571*WEIGHT_LOSS-0.0008959*AVE_INT_LENGTH+1.385*AGE_u7+1.061*AGE_7t12-0.1097*ANTIBIOTICS+0.0005462*event_interval_2+0.0001019*event_interval_diff_2-0.05926*event_interval_ratio_2+0.0005172*event_interval+0.0005206*event_interval_diff-0.169*event_interval_ratio]
merged_cprd[,glm.lp30d:=-6.959+0.1682*AGE_AT_EVT.x+0.06983*GNDR_CD+0.08961*ANTIPYRETIC-0.2105*ATOPICALLERGY-13.08*BEHAVIOUR+0.4461*BLOODS-0.715*BLURRED_VISION-13.19*BREATHLESSNESS-0.4176*CONSTIPATION-0.05972*CONTACT_NON_SPEC-14.17*FAMILY_HISTORY+1.553*FUNGAL+0.135*GASTROINTESTINAL+0.2841*HEADACHE-0.1332*LOWER_RTI-0.6051*NON_ORAL_ABX+2.344*OBESITY+0.1489*PREDNISOLONE-0.5445*RASH-0.2251*SKIN_INFECTIONS+3.766*THIRST-13.74*TIREDNESS-0.1353*UPPER_RTI+0.2007*URINARY+1.457*POLYURIA+0.5099*VOMITING_NAUSEA+0.8363*WEIGHT_LOSS+0.00007436*AVE_INT_LENGTH+1.407*AGE_u7+1.156*AGE_7t12+0.1758*ANTIBIOTICS-0.0004188*event_interval_2+0.0001652*event_interval_diff_2-0.03006*event_interval_ratio_2+0.0007825*event_interval-0.0006898*event_interval_diff-0.09563*event_interval_ratio]
merged_cprd[,glm.lp90d:=-5.637+0.1828*AGE_AT_EVT.x-0.0126*GNDR_CD+0.06161*ANTIPYRETIC+0.0625*ATOPICALLERGY+0.221*BEHAVIOUR+0.09284*BLOODS+0.07675*BLURRED_VISION+1.231*BREATHLESSNESS-0.7041*CONSTIPATION-0.3822*CONTACT_NON_SPEC+1.163*FAMILY_HISTORY+0.706*FUNGAL+0.09585*GASTROINTESTINAL+0.7031*HEADACHE-0.2733*LOWER_RTI-0.1904*NON_ORAL_ABX-10.71*OBESITY+0.5597*PREDNISOLONE+0.1044*RASH+0.04491*SKIN_INFECTIONS+1.203*THIRST-0.3088*TIREDNESS+0.01773*UPPER_RTI+0.1942*URINARY+0.5996*POLYURIA-0.027*VOMITING_NAUSEA+0.3367*WEIGHT_LOSS-0.0009503*AVE_INT_LENGTH+1.333*AGE_u7+0.946*AGE_7t12+0.05466*ANTIBIOTICS-0.00002175*event_interval_2+0.00001121*event_interval_diff_2-0.02717*event_interval_ratio_2+0.001396*event_interval-0.001181*event_interval_diff-0.0239*event_interval_ratio]
merged_cprd[,glm.lp180d:=-4.633+0.1409*AGE_AT_EVT.x-0.08406*GNDR_CD-0.1434*ANTIPYRETIC+0.1506*ATOPICALLERGY-0.006977*BEHAVIOUR+0.3182*BLOODS-0.51*BLURRED_VISION-0.8605*BREATHLESSNESS-0.6299*CONSTIPATION+0.07547*CONTACT_NON_SPEC+0.6097*FAMILY_HISTORY+0.1168*FUNGAL+0.2472*GASTROINTESTINAL+0.3676*HEADACHE-0.02865*LOWER_RTI-0.003307*NON_ORAL_ABX+0.7853*OBESITY+0.1659*PREDNISOLONE+0.06583*RASH-0.04159*SKIN_INFECTIONS+0.7926*THIRST+0.3185*TIREDNESS-0.0352*UPPER_RTI+0.2101*URINARY-0.197*POLYURIA+0.5436*VOMITING_NAUSEA+0.01665*WEIGHT_LOSS+0.0008287*AVE_INT_LENGTH+0.9202*AGE_u7+0.8994*AGE_7t12+0.06361*ANTIBIOTICS+0.0001785*event_interval_2-0.00005*event_interval_diff_2-0.02058*event_interval_ratio_2-0.0006489*event_interval+0.0003468*event_interval_diff+0.003391*event_interval_ratio]
merged_cprd[,glm.lp366d:=-3.901+0.126*AGE_AT_EVT.x+0.05657*GNDR_CD-0.01655*ANTIPYRETIC+0.2281*ATOPICALLERGY-0.1023*BEHAVIOUR+0.06463*BLOODS+0.05994*BLURRED_VISION+0.1617*BREATHLESSNESS-0.6596*CONSTIPATION+0.05925*CONTACT_NON_SPEC+0.8528*FAMILY_HISTORY-0.1802*FUNGAL+0.1886*GASTROINTESTINAL+0.1689*HEADACHE-0.06483*LOWER_RTI-0.07952*NON_ORAL_ABX+0.4948*OBESITY+0.3543*PREDNISOLONE-0.07097*RASH+0.071*SKIN_INFECTIONS-0.5833*THIRST+0.6127*TIREDNESS+0.03756*UPPER_RTI+0.2532*URINARY-0.1316*POLYURIA+0.1067*VOMITING_NAUSEA+0.08192*WEIGHT_LOSS+0.001101*AVE_INT_LENGTH+1.025*AGE_u7+0.9069*AGE_7t12+0.1764*ANTIBIOTICS-0.0005696*event_interval_2+0.0006641*event_interval_diff_2-0.01275*event_interval_ratio_2-0.0006466*event_interval+0.0004292*event_interval_diff-0.01362*event_interval_ratio]
merged_cprd[,glm.p1d.t:=exp(glm.lp1d)/(1+exp(glm.lp1d))]
merged_cprd[,glm.p7d.t:=exp(glm.lp7d)/(1+exp(glm.lp7d))]
merged_cprd[,glm.p14d.t:=exp(glm.lp14d)/(1+exp(glm.lp14d))]
merged_cprd[,glm.p30d.t:=exp(glm.lp30d)/(1+exp(glm.lp30d))]
merged_cprd[,glm.p90d.t:=exp(glm.lp90d)/(1+exp(glm.lp90d))]
merged_cprd[,glm.p180d.t:=exp(glm.lp180d)/(1+exp(glm.lp180d))]
merged_cprd[,glm.p366d.t:=exp(glm.lp366d)/(1+exp(glm.lp366d))]

# Adjust these for the fact that only 40000 controls were included in each logistic regression
ccps1<-(40000-1385)/(34754400-1385)
ccps7<-(40000-721)/(34753015-721)
ccps14<-(40000-349)/(34752294-349)
ccps30<-(40000-503)/(34751945-503)
ccps90<-(40000-1491)/(34751442-1491)
ccps180<-(40000-2071)/(34749951-2071)
ccps366<-(40000-4625)/(34747880-4625)

ccps<-c(ccps1,ccps7,ccps14,ccps30,ccps90,ccps180,ccps366)

merged_cprd[,glm.p1d:=ccps[1]*glm.p1d.t/(1-(1-ccps[1])*glm.p1d.t)]
merged_cprd[,glm.cp7d:=ccps[2]*glm.p7d.t/(1-(1-ccps[2])*glm.p7d.t)]
merged_cprd[,glm.cp14d:=ccps[3]*glm.p14d.t/(1-(1-ccps[3])*glm.p14d.t)]
merged_cprd[,glm.cp30d:=ccps[4]*glm.p30d.t/(1-(1-ccps[4])*glm.p30d.t)]
merged_cprd[,glm.cp90d:=ccps[5]*glm.p90d.t/(1-(1-ccps[5])*glm.p90d.t)]
merged_cprd[,glm.cp180d:=ccps[6]*glm.p180d.t/(1-(1-ccps[6])*glm.p180d.t)]
merged_cprd[,glm.cp366d:=ccps[7]*glm.p366d.t/(1-(1-ccps[7])*glm.p366d.t)]

merged_cprd[,glm.p7d:=glm.p1d+(1-glm.p1d)*glm.cp7d]
merged_cprd[,glm.p14d:=glm.p7d+(1-glm.p7d)*glm.cp14d]
merged_cprd[,glm.p30d:=glm.p14d+(1-glm.p14d)*glm.cp30d]
merged_cprd[,glm.p90d:=glm.p30d+(1-glm.p30d)*glm.cp90d]
merged_cprd[,glm.p180d:=glm.p90d+(1-glm.p90d)*glm.cp180d]
merged_cprd[,glm.p366d:=glm.p180d+(1-glm.p180d)*glm.cp366d]
  
####################################################################################################################
## For later benchmarking, create a 'chance' random alert, and ones based on all 4 'T's, any 3 of the 4 'T's, etc ##
####################################################################################################################

merged_cprd[,chance1.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance2.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance3.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance4.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance5.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance6.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance7.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance8.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance9.p:=runif(nrow(merged_cprd))]
merged_cprd[,chance10.p:=runif(nrow(merged_cprd))]

merged_cprd[,FourT:=THIRST==1 & TIREDNESS==1 & WEIGHT_LOSS==1 & POLYURIA==1]
merged_cprd[,ThreeT:=(THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=3]
merged_cprd[,TwoT:=(THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=2]
merged_cprd[,OneT:=(THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=1]


##########################################################################
## Calculate effort and benefit for the 4T, 3T, 2T and 1T alert systems ##
##########################################################################

merged_cprd[,days_from_T1D:=time_until_diagnosis]
merged_cprd[,min_days_from_T1D:=min(time_until_diagnosis),by=new_id2]
table(merged_cprd[EVENT_SEQN==1 & is.na(days_from_T1D)==FALSE][,min_days_from_T1D]<=1)

merged_cprd[,included_now:=(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0]
merged_cprd[,included_atall:=max(included_now),by=new_id2]

#ALL FOUR Ts
merged_cprd[,FourT_now:=(FourT==TRUE) & (nont1==FALSE) & (days_from_T1D<=90) & (permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0]
merged_cprd[,FourT_maxnow:=max(FourT_now),by=new_id2]
#benefit
FourT.benefit=table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,FourT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,FourT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,FourT_maxnow])[2])
SE.FourT.benefit=sqrt(FourT.benefit*(1-FourT.benefit)/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,FourT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,FourT_maxnow])[2]))
#effort
FourT.effort=table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,FourT])[2]/(table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,FourT])[1]+table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,FourT])[2])

#ANY THREE Ts
merged_cprd[,ThreeT_now:=(ThreeT==TRUE) & (nont1==FALSE) & (days_from_T1D<=90) & (permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0]
merged_cprd[,ThreeT_maxnow:=max(ThreeT_now),by=new_id2]
#benefit
ThreeT.benefit=table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[2])
SE.ThreeT.benefit=sqrt(ThreeT.benefit*(1-ThreeT.benefit)/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[2]))
#effort
ThreeT.effort=table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,ThreeT])[2]/(table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,ThreeT])[1]+table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,ThreeT])[2])

#ANY TWO Ts
merged_cprd[,TwoT_now:=(TwoT==TRUE) & (nont1==FALSE) & (days_from_T1D<=90) & (permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0]
merged_cprd[,TwoT_maxnow:=max(TwoT_now),by=new_id2]
#benefit
TwoT.benefit=table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,TwoT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,TwoT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,TwoT_maxnow])[2])
SE.TwoT.benefit=sqrt(TwoT.benefit*(1-TwoT.benefit)/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,TwoT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,TwoT_maxnow])[2]))
#effort
TwoT.effort=table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,TwoT])[2]/(table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,TwoT])[1]+table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,TwoT])[2])

#ANY ONE T
merged_cprd[,OneT_now:=(OneT==TRUE) & (nont1==FALSE) & (days_from_T1D<=90) & (permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0]
merged_cprd[,OneT_maxnow:=max(OneT_now),by=new_id2]
#benefit
OneT.benefit=table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit=sqrt(OneT.benefit*(1-OneT.benefit)/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))
#effort
OneT.effort=table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[2]/(table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[1]+table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[2])

#We will always look at effort/benefit also within subgroups defined by DKA at diagnosis and age at diagnosis
#ANY ONE T & DKA
#benefit
OneT.benefit.DKA=table(merged_cprd[diagnosis_in_DKA==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[diagnosis_in_DKA==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[diagnosis_in_DKA==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit.DKA=sqrt(OneT.benefit.DKA*(1-OneT.benefit.DKA)/(table(merged_cprd[diagnosis_in_DKA==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[diagnosis_in_DKA==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))

#ANY ONE T & u6
#benefit
OneT.benefit.u6=table(merged_cprd[AGE_AT_T1D_DIAG_u6==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[AGE_AT_T1D_DIAG_u6==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[AGE_AT_T1D_DIAG_u6==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit.u6=sqrt(OneT.benefit.u6*(1-OneT.benefit.u6)/(table(merged_cprd[AGE_AT_T1D_DIAG_u6==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[AGE_AT_T1D_DIAG_u6==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))

#ANY ONE T & 7t12
#benefit
OneT.benefit.7t12=table(merged_cprd[AGE_AT_T1D_DIAG_7t12==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[AGE_AT_T1D_DIAG_7t12==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[AGE_AT_T1D_DIAG_7t12==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit.7t12=sqrt(OneT.benefit.7t12*(1-OneT.benefit.7t12)/(table(merged_cprd[AGE_AT_T1D_DIAG_7t12==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[AGE_AT_T1D_DIAG_7t12==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))

#ANY ONE T & 13p
#benefit
OneT.benefit.13p=table(merged_cprd[AGE_AT_T1D_DIAG_13p==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[AGE_AT_T1D_DIAG_13p==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[AGE_AT_T1D_DIAG_13p==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit.13p=sqrt(OneT.benefit.13p*(1-OneT.benefit.13p)/(table(merged_cprd[AGE_AT_T1D_DIAG_13p==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[AGE_AT_T1D_DIAG_13p==1 & EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))

OneT.benefit.DKA
OneT.benefit.DKA-1.96*SE.OneT.benefit.DKA
OneT.benefit.DKA+1.96*SE.OneT.benefit.DKA

OneT.benefit.u6
OneT.benefit.u6-1.96*SE.OneT.benefit.u6
OneT.benefit.u6+1.96*SE.OneT.benefit.u6

OneT.benefit.7t12
OneT.benefit.7t12-1.96*SE.OneT.benefit.7t12
OneT.benefit.7t12+1.96*SE.OneT.benefit.7t12

OneT.benefit.13p
OneT.benefit.13p-1.96*SE.OneT.benefit.13p
OneT.benefit.13p+1.96*SE.OneT.benefit.13p

merged_cprd[, days_ant:=ifelse(OneT_now=="TRUE" & nont1==FALSE & days_from_T1D<=90,days_from_T1D,0)]

merged_cprd[, max_days_ant:=max(days_ant),by=new_id2]

OneT.ma<-mean(merged_cprd[EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)
n.OneT<-sum(merged_cprd[EVENT_SEQN==1 & OneT_maxnow==1][,EVENT_SEQN],na.rm=TRUE)
se.OneT.ma<-sd(merged_cprd[EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)/(sqrt(n.OneT))

OneT.ma.dka<-mean(merged_cprd[diagnosis_in_DKA==1 & EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)
n.OneT.dka<-sum(merged_cprd[diagnosis_in_DKA==1 & EVENT_SEQN==1 & OneT_maxnow==1][,EVENT_SEQN],na.rm=TRUE)
se.OneT.ma.dka<-sd(merged_cprd[diagnosis_in_DKA==1 & EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)/(sqrt(n.OneT.dka))

OneT.ma.u6<-mean(merged_cprd[AGE_AT_T1D_DIAG_u6==1 & EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)
n.OneT.u6<-sum(merged_cprd[AGE_AT_T1D_DIAG_u6==1 & EVENT_SEQN==1 & OneT_maxnow==1][,EVENT_SEQN],na.rm=TRUE)
se.OneT.ma.u6<-sd(merged_cprd[AGE_AT_T1D_DIAG_u6==1 & EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)/(sqrt(n.OneT.u6))

OneT.ma.7t12<-mean(merged_cprd[AGE_AT_T1D_DIAG_7t12==1 & EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)
n.OneT.7t12<-sum(merged_cprd[AGE_AT_T1D_DIAG_7t12==1 & EVENT_SEQN==1 & OneT_maxnow==1][,EVENT_SEQN],na.rm=TRUE)
se.OneT.ma.7t12<-sd(merged_cprd[AGE_AT_T1D_DIAG_7t12==1 & EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)/(sqrt(n.OneT.7t12))

OneT.ma.13p<-mean(merged_cprd[AGE_AT_T1D_DIAG_13p==1 & EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)
n.OneT.13p<-sum(merged_cprd[AGE_AT_T1D_DIAG_13p==1 & EVENT_SEQN==1 & OneT_maxnow==1][,EVENT_SEQN],na.rm=TRUE)
se.OneT.ma.13p<-sd(merged_cprd[AGE_AT_T1D_DIAG_13p==1 & EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE)/(sqrt(n.OneT.13p))

OneT.ma
OneT.ma-1.96*se.OneT.ma
OneT.ma+1.96*se.OneT.ma

OneT.ma.dka
OneT.ma.dka-1.96*se.OneT.ma.dka
OneT.ma.dka+1.96*se.OneT.ma.dka

OneT.ma.u6
OneT.ma.u6-1.96*se.OneT.ma.u6
OneT.ma.u6+1.96*se.OneT.ma.u6

OneT.ma.7t12
OneT.ma.7t12-1.96*se.OneT.ma.7t12
OneT.ma.7t12+1.96*se.OneT.ma.7t12

OneT.ma.13p
OneT.ma.13p-1.96*se.OneT.ma.13p
OneT.ma.13p+1.96*se.OneT.ma.13p

OneT.75c<-quantile(merged_cprd[EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],probs=c(0.75),na.rm=TRUE)
se.OneT.75c<-sqrt(75*25)/(100*sqrt(n.OneT)*(dnorm(OneT.75c,OneT.ma,sd(merged_cprd[EVENT_SEQN==1 & OneT_maxnow==1][,max_days_ant],na.rm=TRUE))))

#Repeat for a 45 day diagnosis window
#ANY ONE T
merged_cprd[,OneT_now:=(OneT==TRUE) & (nont1==FALSE) & (days_from_T1D<=45) & (permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0]
merged_cprd[,OneT_maxnow:=max(OneT_now),by=new_id2]
#benefit
OneT.benefit.45d=table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit.45d=sqrt(OneT.benefit.45d*(1-OneT.benefit.45d)/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))
#effort
OneT.effort.45d=table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[2]/(table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[1]+table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[2])

#Repeat for a 14 day diagnosis window
#ANY ONE T
merged_cprd[,OneT_now:=(OneT==TRUE) & (nont1==FALSE) & (days_from_T1D<=14) & (permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0]
merged_cprd[,OneT_maxnow:=max(OneT_now),by=new_id2]
#benefit
OneT.benefit.14d=table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit.14d=sqrt(OneT.benefit.14d*(1-OneT.benefit.14d)/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))
#effort
OneT.effort.14d=table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[2]/(table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[1]+table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[2])

#Repeat for a 180 day diagnosis window
#ANY ONE T
merged_cprd[,OneT_now:=(OneT==TRUE) & (nont1==FALSE) & (days_from_T1D<=180) & (permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0]
merged_cprd[,OneT_maxnow:=max(OneT_now),by=new_id2]
#benefit
OneT.benefit.180d=table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit.180d=sqrt(OneT.benefit.180d*(1-OneT.benefit.180d)/(table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & susp_t1d_no_conf_in_diag_date==FALSE & nont1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))
#effort
OneT.effort.180d=table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[2]/(table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[1]+table(merged_cprd[(permitted==1) & susp_t1d_no_conf_in_diag_date==FALSE & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & check_timings==TRUE & duplicate==0][,OneT])[2])

#NOW FOR SENSITIVITY ANALYSIS - INCLUDING THE SUSPECTED T1D WITH NO CONF IN THEIR DATE AT DIAG
merged_cprd[,susp_t1d_diag_dt:=ifelse(is.na(t1d_diag_dt)==FALSE,t1d_diag_dt,ifelse(susp_t1d_no_conf_in_diag_date==FALSE,NA,min(c(first_T1D_med_in_fup,first_T1D_HES_in_fup,first_T1D_prod_in_fup),na.rm=TRUE)))]

merged_cprd[,AGE_AT_susp_T1D_DIAG:=(susp_t1d_diag_dt-as.numeric(imp_birth_date))/365.25]

merged_cprd[,days_from_susp_T1D:=susp_t1d_diag_dt-as.numeric(EVENT_DT)]

merged_cprd[,non_susp_t1:=(is.na(susp_t1d_diag_dt)==TRUE | (is.na(susp_t1d_diag_dt)==FALSE & AGE_AT_susp_T1D_DIAG>=15.0098) | (is.na(susp_t1d_diag_dt)==FALSE & susp_t1d_diag_dt>as.Date("2016-12-31")))]

merged_cprd<-merged_cprd[, susp_check_timings:=EVENT_DT<=susp_t1d_diag_dt | is.na(susp_t1d_diag_dt)]

merged_cprd[,included_now:=(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0]
merged_cprd[,included_atall:=max(included_now),by=new_id2]

#ALL FOUR Ts
merged_cprd[,FourT_now:=(FourT==TRUE) & (non_susp_t1==FALSE) & (days_from_susp_T1D<=90) & (permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0]
merged_cprd[,FourT_maxnow:=max(FourT_now),by=new_id2]
#benefit
FourT.benefit.inclsusp=table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,FourT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,FourT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,FourT_maxnow])[2])
SE.FourT.benefit.inclsusp=sqrt(FourT.benefit.inclsusp*(1-FourT.benefit.inclsusp)/(table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,FourT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,FourT_maxnow])[2]))
#effort
FourT.effort.inclsusp=table(merged_cprd[(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,FourT])[2]/(table(merged_cprd[(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,FourT])[1]+table(merged_cprd[(permitted==1)  & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,FourT])[2])

#ANY THREE Ts
merged_cprd[,ThreeT_now:=(ThreeT==TRUE) & (non_susp_t1==FALSE) & (days_from_susp_T1D<=90) & (permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0]
merged_cprd[,ThreeT_maxnow:=max(ThreeT_now),by=new_id2]
#benefit
ThreeT.benefit.inclsusp=table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[2])
SE.ThreeT.benefit.inclsusp=sqrt(ThreeT.benefit.inclsusp*(1-ThreeT.benefit.inclsusp)/(table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,ThreeT_maxnow])[2]))
#effort
ThreeT.effort.inclsusp=table(merged_cprd[(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,ThreeT])[2]/(table(merged_cprd[(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,ThreeT])[1]+table(merged_cprd[(permitted==1)  & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,ThreeT])[2])

#ANY TWO Ts
merged_cprd[,TwoT_now:=(TwoT==TRUE) & (non_susp_t1==FALSE) & (days_from_susp_T1D<=90) & (permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0]
merged_cprd[,TwoT_maxnow:=max(TwoT_now),by=new_id2]
#benefit
TwoT.benefit.inclsusp=table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,TwoT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,TwoT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,TwoT_maxnow])[2])
SE.TwoT.benefit.inclsusp=sqrt(TwoT.benefit.inclsusp*(1-TwoT.benefit.inclsusp)/(table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,TwoT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,TwoT_maxnow])[2]))
#effort
TwoT.effort.inclsusp=table(merged_cprd[(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,TwoT])[2]/(table(merged_cprd[(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,TwoT])[1]+table(merged_cprd[(permitted==1)  & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,TwoT])[2])

#ANY ONE T
merged_cprd[,OneT_now:=(OneT==TRUE) & (non_susp_t1==FALSE) & (days_from_susp_T1D<=90) & (permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0]
merged_cprd[,OneT_maxnow:=max(OneT_now),by=new_id2]
#benefit
OneT.benefit.inclsusp=table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]/(table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,OneT_maxnow])[2])
SE.OneT.benefit.inclsusp=sqrt(OneT.benefit.inclsusp*(1-OneT.benefit.inclsusp)/(table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,OneT_maxnow])[1]+table(merged_cprd[EVENT_SEQN==1 & non_susp_t1==FALSE & included_atall==TRUE][,OneT_maxnow])[2]))
#effort
OneT.effort.inclsusp=table(merged_cprd[(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,OneT])[2]/(table(merged_cprd[(permitted==1) & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,OneT])[1]+table(merged_cprd[(permitted==1)  & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_check_timings==TRUE & duplicate==0][,OneT])[2])

###############################################
## At this point, the SL objects are read in ##
###############################################

################################
## Predict using SuperLearner ##
################################

newdata = as.data.frame(subset(
  merged_cprd,
  select = -c(
    EVENT_DT,
    new_id2,
    yob,
    mob,
    imp_birth_date,
    first_T1D_HES_in_fup,
    first_T1D_med_in_fup,
    first_T1D_prod_in_fup,
    first_DKA_HES_in_fup,
    t1d_diag_dt,
    admimeth_grp,
    AGE_AT_EVT_days,
    EVENT_SEQN,
    Asthma_meds,
    time_until_diagnosis
  )
))

v1<-colnames(newdata)
v2<-SL_object_1d_with2lags_dataremoved$varNames
m<-match(v2,v1)

newdata<-newdata[,c(m)]

for(i in 1:44) {
  j=(i-1)*1000000+1
  k=i*1000000
  if (i==44) {
    k=nrow(newdata)
  }
  newdata_small<-newdata[j:k,]
  start_time <- Sys.time()
  p1d<-predict(SL_object_1d_with2lags_dataremoved,newdata=newdata_small,onlySL=TRUE,verbose=TRUE)
  end_time <- Sys.time()
  sprintf("Time taken %f", end_time - start_time)
  saveRDS(p1d,file = paste(path_to_SLobj,"/v2022_p1d_",i,".rds", sep = ""))
}

p1d<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p1d_1.rds", sep = ""))$pred
for(i in 2:44) {
  p1d_new<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p1d_",i,".rds", sep = ""))$pred
  p1d<-rbind(p1d,p1d_new)
}

saveRDS(p1d,file = paste(path_to_SLobj,"/v2_Sept_2022_p1d_all.rds",sep = ""))

p7d<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p7d_1.rds", sep = ""))$pred
for(i in 2:44) {
  p7d_new<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p7d_",i,".rds", sep = ""))$pred
  p7d<-rbind(p7d,p7d_new)
}

saveRDS(p7d,file = paste(path_to_SLobj,"/v2_Sept_2022_p7d_all.rds",sep = ""))

p14d<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p14d_1.rds", sep = ""))$pred
for(i in 2:44) {
  p14d_new<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p14d_",i,".rds", sep = ""))$pred
  p14d<-rbind(p14d,p14d_new)
}

saveRDS(p14d,file = paste(path_to_SLobj,"/v2_Sept_2022_p14d_all.rds",sep = ""))

p30d<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p30d_1.rds", sep = ""))$pred
for(i in 2:44) {
  p30d_new<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p30d_",i,".rds", sep = ""))$pred
  p30d<-rbind(p30d,p30d_new)
}

saveRDS(p30d,file = paste(path_to_SLobj,"/v2_Sept_2022_p30d_all.rds",sep = ""))

p90d<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p90d_1.rds", sep = ""))$pred
for(i in 2:44) {
  p90d_new<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p90d_",i,".rds", sep = ""))$pred
  p90d<-rbind(p90d,p90d_new)
}

saveRDS(p90d,file = paste(path_to_SLobj,"/v2_Sept_2022_p90d_all.rds",sep = ""))

p180d<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p180d_1.rds", sep = ""))$pred
for(i in 2:44) {
  p180d_new<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p180d_",i,".rds", sep = ""))$pred
  p180d<-rbind(p180d,p180d_new)
}

saveRDS(p180d,file = paste(path_to_SLobj,"/v2_Sept_2022_p180d_all.rds",sep = ""))

p366d<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p366d_1.rds", sep = ""))$pred
for(i in 2:44) {
  p366d_new<-readRDS(file = paste(path_to_SLobj,"/v2_Sept_2022_p366d_",i,".rds", sep = ""))$pred
  p366d<-rbind(p366d,p366d_new)
}

saveRDS(p366d,file = paste(path_to_SLobj,"/v2_Sept_2022_p366d_all.rds",sep = ""))

############################
## Performance evaluation ##
############################

merged_cprd<-merged_cprd[check_timings==TRUE]

merged_cprd[,sl.p1d.t:=p1d]
merged_cprd[,sl.cp7d.t:=p7d]
merged_cprd[,sl.cp14d.t:=p14d]
merged_cprd[,sl.cp30d.t:=p30d]
merged_cprd[,sl.cp90d.t:=p90d]
merged_cprd[,sl.cp180d.t:=p180d]
merged_cprd[,sl.cp366d.t:=p366d]

merged_cprd[,sl.p1d:=ccps[1]*sl.p1d.t/(1-(1-ccps[1])*sl.p1d.t)]
merged_cprd[,sl.cp7d:=ccps[2]*sl.cp7d.t/(1-(1-ccps[2])*sl.cp7d.t)]
merged_cprd[,sl.cp14d:=ccps[3]*sl.cp14d.t/(1-(1-ccps[3])*sl.cp14d.t)]
merged_cprd[,sl.cp30d:=ccps[4]*sl.cp30d.t/(1-(1-ccps[4])*sl.cp30d.t)]
merged_cprd[,sl.cp90d:=ccps[5]*sl.cp90d.t/(1-(1-ccps[5])*sl.cp90d.t)]
merged_cprd[,sl.cp180d:=ccps[6]*sl.cp180d.t/(1-(1-ccps[6])*sl.cp180d.t)]
merged_cprd[,sl.cp366d:=ccps[7]*sl.cp366d.t/(1-(1-ccps[7])*sl.cp366d.t)]

merged_cprd[,sl.p7d:=sl.p1d+(1-sl.p1d)*sl.cp7d]
merged_cprd[,sl.p14d:=sl.p7d+(1-sl.p7d)*sl.cp14d]
merged_cprd[,sl.p30d:=sl.p14d+(1-sl.p14d)*sl.cp30d]
merged_cprd[,sl.p90d:=sl.p30d+(1-sl.p30d)*sl.cp90d]
merged_cprd[,sl.p180d:=sl.p90d+(1-sl.p90d)*sl.cp180d]
merged_cprd[,sl.p366d:=sl.p180d+(1-sl.p180d)*sl.cp366d]

merged_cprd[,T1D:=nont1==FALSE]
merged_cprd[,ALF_PE:=new_id2]

prevalence_table<-merged_cprd[EVENT_SEQN==1 & included_atall==1][, .N, by=T1D]
prev<-prevalence_table[2,N]/(prevalence_table[1,N]+prevalence_table[2,N])

merged_cprd[,su:=runif(1),by=new_id2]
merged_cprd[,days_from_T1D:=time_until_diagnosis]

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE]

eb_sl<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
eb_sl_45<-eb.calc(merged_cprd_small,wind_days=45,cutoff=1)
eb_sl_14<-eb.calc(merged_cprd_small,wind_days=14,cutoff=1)
eb_sl_180<-eb.calc(merged_cprd_small,wind_days=180,cutoff=1)

#compare with logistic regression
merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE]
eb_glm<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

#compare with chance
merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE]
eb_chance1<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
eb_chance1_45<-eb.calc(merged_cprd_small,wind_days=45,cutoff=1)
eb_chance1_14<-eb.calc(merged_cprd_small,wind_days=14,cutoff=1)
eb_chance1_180<-eb.calc(merged_cprd_small,wind_days=180,cutoff=1)


#################################################################
## The remaining code generates the various Figures and Tables ##
#################################################################

eb_sl[[1]]<-cbind(eb_sl[[1]],eb_sl[[1]][,2]-1.96*eb_sl[[1]][,18],eb_sl[[1]][,2]+1.96*eb_sl[[1]][,18])
eb_glm[[1]]<-cbind(eb_glm[[1]],eb_glm[[1]][,2]-1.96*eb_glm[[1]][,18],eb_glm[[1]][,2]+1.96*eb_glm[[1]][,18])
eb_chance1[[1]]<-cbind(eb_chance1[[1]],eb_chance1[[1]][,2]-1.96*eb_chance1[[1]][,18],eb_chance1[[1]][,2]+1.96*eb_chance1[[1]][,18])
eb_sl_45[[1]]<-cbind(eb_sl_45[[1]],eb_sl_45[[1]][,2]-1.96*eb_sl_45[[1]][,18],eb_sl_45[[1]][,2]+1.96*eb_sl_45[[1]][,18])
eb_chance1_45[[1]]<-cbind(eb_chance1_45[[1]],eb_chance1_45[[1]][,2]-1.96*eb_chance1_45[[1]][,18],eb_chance1_45[[1]][,2]+1.96*eb_chance1_45[[1]][,18])
eb_sl_14[[1]]<-cbind(eb_sl_14[[1]],eb_sl_14[[1]][,2]-1.96*eb_sl_14[[1]][,18],eb_sl_14[[1]][,2]+1.96*eb_sl_14[[1]][,18])
eb_chance1_14[[1]]<-cbind(eb_chance1_14[[1]],eb_chance1_14[[1]][,2]-1.96*eb_chance1_14[[1]][,18],eb_chance1_14[[1]][,2]+1.96*eb_chance1_14[[1]][,18])
eb_sl_180[[1]]<-cbind(eb_sl_180[[1]],eb_sl_180[[1]][,2]-1.96*eb_sl_180[[1]][,18],eb_sl_180[[1]][,2]+1.96*eb_sl_180[[1]][,18])
eb_chance1_180[[1]]<-cbind(eb_chance1_180[[1]],eb_chance1_180[[1]][,2]-1.96*eb_chance1_180[[1]][,18],eb_chance1_180[[1]][,2]+1.96*eb_chance1_180[[1]][,18])

eb_sl[[1]]<-cbind(eb_sl[[1]],eb_sl[[1]][,7]-1.96*eb_sl[[1]][,17],eb_sl[[1]][,7]+1.96*eb_sl[[1]][,17])
eb_glm[[1]]<-cbind(eb_glm[[1]],eb_glm[[1]][,7]-1.96*eb_glm[[1]][,17],eb_glm[[1]][,7]+1.96*eb_glm[[1]][,17])
eb_chance1[[1]]<-cbind(eb_chance1[[1]],eb_chance1[[1]][,7]-1.96*eb_chance1[[1]][,17],eb_chance1[[1]][,7]+1.96*eb_chance1[[1]][,17])
eb_sl_45[[1]]<-cbind(eb_sl_45[[1]],eb_sl_45[[1]][,7]-1.96*eb_sl_45[[1]][,17],eb_sl_45[[1]][,7]+1.96*eb_sl_45[[1]][,17])
eb_chance1_45[[1]]<-cbind(eb_chance1_45[[1]],eb_chance1_45[[1]][,7]-1.96*eb_chance1_45[[1]][,17],eb_chance1_45[[1]][,7]+1.96*eb_chance1_45[[1]][,17])
eb_sl_14[[1]]<-cbind(eb_sl_14[[1]],eb_sl_14[[1]][,7]-1.96*eb_sl_14[[1]][,17],eb_sl_14[[1]][,7]+1.96*eb_sl_14[[1]][,17])
eb_chance1_14[[1]]<-cbind(eb_chance1_14[[1]],eb_chance1_14[[1]][,7]-1.96*eb_chance1_14[[1]][,17],eb_chance1_14[[1]][,7]+1.96*eb_chance1_14[[1]][,17])
eb_sl_180[[1]]<-cbind(eb_sl_180[[1]],eb_sl_180[[1]][,7]-1.96*eb_sl_180[[1]][,17],eb_sl_180[[1]][,7]+1.96*eb_sl_180[[1]][,17])
eb_chance1_180[[1]]<-cbind(eb_chance1_180[[1]],eb_chance1_180[[1]][,7]-1.96*eb_chance1_180[[1]][,17],eb_chance1_180[[1]][,7]+1.96*eb_chance1_180[[1]][,17])

eb_sl[[1]]<-cbind(eb_sl[[1]],eb_sl[[1]][,6]-1.96*eb_sl[[1]][,16],eb_sl[[1]][,6]+1.96*eb_sl[[1]][,16])
eb_glm[[1]]<-cbind(eb_glm[[1]],eb_glm[[1]][,6]-1.96*eb_glm[[1]][,16],eb_glm[[1]][,6]+1.96*eb_glm[[1]][,16])
eb_chance1[[1]]<-cbind(eb_chance1[[1]],eb_chance1[[1]][,6]-1.96*eb_chance1[[1]][,16],eb_chance1[[1]][,6]+1.96*eb_chance1[[1]][,16])
eb_sl_45[[1]]<-cbind(eb_sl_45[[1]],eb_sl_45[[1]][,6]-1.96*eb_sl_45[[1]][,16],eb_sl_45[[1]][,6]+1.96*eb_sl_45[[1]][,16])
eb_chance1_45[[1]]<-cbind(eb_chance1_45[[1]],eb_chance1_45[[1]][,6]-1.96*eb_chance1_45[[1]][,16],eb_chance1_45[[1]][,6]+1.96*eb_chance1_45[[1]][,16])
eb_sl_14[[1]]<-cbind(eb_sl_14[[1]],eb_sl_14[[1]][,6]-1.96*eb_sl_14[[1]][,16],eb_sl_14[[1]][,6]+1.96*eb_sl_14[[1]][,16])
eb_chance1_14[[1]]<-cbind(eb_chance1_14[[1]],eb_chance1_14[[1]][,6]-1.96*eb_chance1_14[[1]][,16],eb_chance1_14[[1]][,6]+1.96*eb_chance1_14[[1]][,16])
eb_sl_180[[1]]<-cbind(eb_sl_180[[1]],eb_sl_180[[1]][,6]-1.96*eb_sl_180[[1]][,16],eb_sl_180[[1]][,6]+1.96*eb_sl_180[[1]][,16])
eb_chance1_180[[1]]<-cbind(eb_chance1_180[[1]],eb_chance1_180[[1]][,6]-1.96*eb_chance1_180[[1]][,16],eb_chance1_180[[1]][,6]+1.96*eb_chance1_180[[1]][,16])

eb_sl=as.data.frame(eb_sl)
eb_glm=as.data.frame(eb_glm)
eb_chance1=as.data.frame(eb_chance1)
eb_sl_45=as.data.frame(eb_sl_45)
eb_sl_14=as.data.frame(eb_sl_14)
eb_sl_180=as.data.frame(eb_sl_180)
eb_chance1_45=as.data.frame(eb_chance1_45)
eb_chance1_14=as.data.frame(eb_chance1_14)
eb_chance1_180=as.data.frame(eb_chance1_180)

eb_sl$Method="SL"
eb_glm$Method="Logistic regression"
eb_chance1$Method="Chance"
#eb_chance2$Method="Chance (2)"
#eb_chance3$Method="Chance (3)"
#eb_chance4$Method="Chance (4)"
#eb_chance5$Method="Chance (5)"
#eb_chance6$Method="Chance (6)"
#eb_chance7$Method="Chance (7)"
#eb_chance8$Method="Chance (8)"
#eb_chance9$Method="Chance (9)"
#eb_chance10$Method="Chance (10)"
eb_sl_45$Method="SL - 45d"
eb_chance1_45$Method="Chance - 45d"
eb_sl_14$Method="SL - 14d"
eb_chance1_14$Method="Chance - 14d"
eb_sl_180$Method="SL - 180d"
eb_chance1_180$Method="Chance - 180d"

colnames(eb_sl)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_sl_45)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_sl_14)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_sl_180)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_glm)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_chance1)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_chance1_45)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_chance1_14)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_chance1_180)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")

eb_all<-rbind(eb_sl,eb_glm,eb_chance1)

eb_all$Method<-factor(eb_all$Method, levels=c("SL", "Logistic regression", "Chance"),labels=c("SL", "Logistic regression", "Chance"))
ltype <- c("SL" = "solid", "Logistic regression" = "longdash", "Chance" = "dotted")

options(OutDec = "·")

plot_sl<-eb_all %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(group=Method,colour=Method,linetype=Method)) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "gray")) +
  geom_ribbon(aes(ymin = X19, ymax = X20, group=Method), alpha = 0.1,linetype=0) +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.6, y=0.5, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.6, y=0.45, label=paste("AUC(LR)=",round(subset(eb_all,Method=="Logistic regression")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=0.6, y=0.4, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance")$AUC[1],3),sep=""), hjust=0,
           color="gray",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of actionable primary care contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D receiving alert during 90-day lead-up to diagnosis") +
  ggtitle("Validation (using CPRD/HES) of the SuperLearner algorithm (developed on SAIL): effort-benefit curve")

eb_all<-rbind(eb_sl,eb_sl_45,eb_sl_14,eb_sl_180,eb_chance1,eb_chance1_45,eb_chance1_14,eb_chance1_180)
eb_all$Method<-factor(eb_all$Method, levels=c("SL", "SL - 45d", "SL - 14d", "SL - 180d", "Chance", "Chance - 45d", "Chance - 14d", "Chance - 180d"), labels=c("SL - 90d", "SL - 45d", "SL - 14d", "SL - 180d", "Chance - 90d", "Chance - 45d", "Chance - 14d", "Chance - 180d"))
ltype <- c("SL - 90d" = "solid", "SL - 45d" = "solid", "SL - 14d" = "solid", "SL - 180d" = "solid","Chance - 90d" = "dotted","Chance - 45d" = "dotted","Chance - 14d" = "dotted","Chance - 180d" = "dotted")
plot_windows<-eb_all %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(group=Method,colour=Method,linetype=Method)) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "orange", "red", "green", "black", "orange", "red", "green")) +
  geom_ribbon(aes(ymin = X19, ymax = X20, group=Method), alpha = 0.1,linetype=0) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort.45d, y=OneT.benefit.45d), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort.14d, y=OneT.benefit.14d), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort.180d, y=OneT.benefit.180d), colour="red", shape=3) +
  annotate(geom="text", x=0.6, y=0.5, label=paste("AUC(SL - 180d)=",round(subset(eb_all,Method=="SL - 180d")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.6, y=0.47, label=paste("AUC(SL - 90d)=",round(subset(eb_all,Method=="SL - 90d")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.6, y=0.44, label=paste("AUC(SL - 45d)=",round(subset(eb_all,Method=="SL - 45d")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.6, y=0.41, label=paste("AUC(SL - 14d)=",round(subset(eb_all,Method=="SL - 14d")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit+0.005, label=" Any 1T (90d)", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort.45d, y=OneT.benefit.45d-0.005, label=" Any 1T (45d)", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort.14d, y=OneT.benefit.14d-0.015, label=" Any 1T (14d)", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort.180d, y=OneT.benefit.180d+0.015, label=" Any 1T (180d)", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of actionable primary care contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D receiving alert during lead-up to diagnosis") +
  ggtitle("Validation (using CPRD/HES) of the SuperLearner algorithm (developed on SAIL): sensitivity analysis varying window length")

eb_all=rbind(eb_sl,eb_glm,eb_chance1)
eb_all$Method<-factor(eb_all$Method, levels=c("SL","Logistic regression","Chance"),labels=c("SL","Logistic regression","Chance"))
ltype <- c("SL" = "solid","Logistic regression" = "longdash","Chance" = "dotted")

plot_sl_mean<-eb_all %>% ggplot(aes(x=X1,y=X7)) +
  geom_line(aes(group=Method,colour=Method,linetype=Method)) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "gray")) +
  geom_ribbon(aes(ymin = X21, ymax = X22, group=Method), alpha = 0.1,linetype=0) +
  #geom_vline(xintercept = .1, color="black") +
  coord_cartesian(ylim=c(-10,30)) +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of actionable primary care contacts (children <15yo) with an alert") +
  ylab("Mean number of days by which diagnosis is anticipated among those correctly alerted") +
  ggtitle("Validation (using CPRD/HES) of the SuperLearner algorithm (developed on SAIL): estimated mean days by which diagnosis is anticipated")

plot_sl_75c<-eb_all %>% ggplot(aes(x=X1,y=X6)) +
  geom_line(aes(group=Method,colour=Method,linetype=Method)) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue","gray")) +
  geom_ribbon(aes(ymin = X23, ymax = X24, group=Method), alpha = 0.1,linetype=0) +
  coord_cartesian(ylim=c(-10,70)) +
  #geom_vline(xintercept = .1, color="black") +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of actionable primary care contacts (children <15yo) with an alert") +
  ylab("75th centile of the distribution of no. of days by which diagnosis is anticipated among those correctly alerted") +
  ggtitle("Validation (using CPRD/HES) of the SuperLearner algorithm (developed on SAIL): estimated 75th centile of the number of days by which diagnosis is anticipated")

saveRDS(eb_all,file = paste(path_to_SLobj,"eb_all.rds",sep = ""))


eb_all<-rbind(eb_sl,eb_sl_45,eb_sl_14,eb_sl_180,eb_chance1,eb_chance1_45,eb_chance1_14,eb_chance1_180)
eb_all$Method<-factor(eb_all$Method, levels=c("SL", "SL - 45d", "SL - 14d", "SL - 180d", "Chance", "Chance - 45d", "Chance - 14d", "Chance - 180d"), labels=c("SL - 90d", "SL - 45d", "SL - 14d", "SL - 180d", "Chance - 90d", "Chance - 45d", "Chance - 14d", "Chance - 180d"))
ltype <- c("SL - 90d" = "solid", "SL - 45d" = "solid", "SL - 14d" = "solid", "SL - 180d" = "solid","Chance - 90d" = "dotted","Chance - 45d" = "dotted","Chance - 14d" = "dotted","Chance - 180d" = "dotted")
plot_mean_diag_windows<-eb_all %>% ggplot(aes(x=X1,y=X7)) +
  coord_cartesian(ylim=c(-10,85)) +
  geom_line(aes(group=Method,colour=Method,linetype=Method)) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "orange", "red", "green", "black", "orange", "red", "green")) +
  geom_ribbon(aes(ymin = X21, ymax = X22, group=Method), alpha = 0.1,linetype=0) +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of actionable primary care contacts (children <15yo) with an alert") +
  ylab("Mean number of days by which diagnosis is anticipated among those correctly alerted") +
  ggtitle("Validation of the SuperLearner algorithm: sensitivity analysis varying window length - mean days anticipation")


plot_75c_windows<-eb_all %>% ggplot(aes(x=X1,y=X6)) +
  geom_line(aes(group=Method,colour=Method,linetype=Method)) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "orange", "red", "green", "black", "orange", "red", "green")) +
  geom_ribbon(aes(ymin = X23, ymax = X24, group=Method), alpha = 0.1,linetype=0) +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of actionable primary care contacts (children <15yo) with an alert") +
  ylab("75th centile of the distribution of no. of days by which diagnosis is anticipated among those correctly alerted") +
  ggtitle("Validation of the SuperLearner algorithm: sensitivity analysis varying window length - 75th centile days anticipation")


merged_cprd[,T1D:=non_susp_t1==FALSE]

prevalence_table<-merged_cprd[EVENT_SEQN==1 & included_atall==1][, .N, by=T1D]
prev<-prevalence_table[2,N]/(prevalence_table[1,N]+prevalence_table[2,N])


merged_cprd[,days_from_T1D:=days_from_susp_T1D]


merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1]
eb_sl_inclsusp<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1]
eb_glm_inclsusp<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1]
eb_chance1_inclsusp<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1,short=TRUE)



eb_sl_inclsusp[[1]]<-cbind(eb_sl_inclsusp[[1]],eb_sl_inclsusp[[1]][,2]-1.96*eb_sl_inclsusp[[1]][,18],eb_sl_inclsusp[[1]][,2]+1.96*eb_sl_inclsusp[[1]][,18])
eb_glm_inclsusp[[1]]<-cbind(eb_glm_inclsusp[[1]],eb_glm_inclsusp[[1]][,2]-1.96*eb_glm_inclsusp[[1]][,18],eb_glm_inclsusp[[1]][,2]+1.96*eb_glm_inclsusp[[1]][,18])
eb_chance1_inclsusp[[1]]<-cbind(eb_chance1_inclsusp[[1]],eb_chance1_inclsusp[[1]][,2]-1.96*eb_chance1_inclsusp[[1]][,18],eb_chance1_inclsusp[[1]][,2]+1.96*eb_chance1_inclsusp[[1]][,18])

eb_sl_inclsusp[[1]]<-cbind(eb_sl_inclsusp[[1]],eb_sl_inclsusp[[1]][,7]-1.96*eb_sl_inclsusp[[1]][,17],eb_sl_inclsusp[[1]][,7]+1.96*eb_sl_inclsusp[[1]][,17])
eb_glm_inclsusp[[1]]<-cbind(eb_glm_inclsusp[[1]],eb_glm_inclsusp[[1]][,7]-1.96*eb_glm_inclsusp[[1]][,17],eb_glm_inclsusp[[1]][,7]+1.96*eb_glm_inclsusp[[1]][,17])
eb_chance1_inclsusp[[1]]<-cbind(eb_chance1_inclsusp[[1]],eb_chance1_inclsusp[[1]][,7]-1.96*eb_chance1_inclsusp[[1]][,17],eb_chance1_inclsusp[[1]][,7]+1.96*eb_chance1_inclsusp[[1]][,17])

eb_sl_inclsusp[[1]]<-cbind(eb_sl_inclsusp[[1]],eb_sl_inclsusp[[1]][,6]-1.96*eb_sl_inclsusp[[1]][,16],eb_sl_inclsusp[[1]][,6]+1.96*eb_sl_inclsusp[[1]][,16])
eb_glm_inclsusp[[1]]<-cbind(eb_glm_inclsusp[[1]],eb_glm_inclsusp[[1]][,6]-1.96*eb_glm_inclsusp[[1]][,16],eb_glm_inclsusp[[1]][,6]+1.96*eb_glm_inclsusp[[1]][,16])
eb_chance1_inclsusp[[1]]<-cbind(eb_chance1_inclsusp[[1]],eb_chance1_inclsusp[[1]][,6]-1.96*eb_chance1_inclsusp[[1]][,16],eb_chance1_inclsusp[[1]][,6]+1.96*eb_chance1_inclsusp[[1]][,16])

eb_sl_inclsusp=as.data.frame(eb_sl_inclsusp)
eb_glm_inclsusp=as.data.frame(eb_glm_inclsusp)
eb_chance1_inclsusp=as.data.frame(eb_chance1_inclsusp)

eb_sl_inclsusp$Method="SL"
eb_glm_inclsusp$Method="Logistic regression"
eb_chance1_inclsusp$Method="Chance"

colnames(eb_sl_inclsusp)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_glm_inclsusp)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")
colnames(eb_chance1_inclsusp)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","X17","X18","X19","X20","X21","X22","X23","X24","AUC","end","X25","X26","X27","X28","X29","Method")

eb_all<-rbind(eb_sl_inclsusp,eb_glm_inclsusp,eb_chance1_inclsusp)

eb_all$Method<-factor(eb_all$Method, levels=c("SL", "Logistic regression", "Chance"),labels=c("SL", "Logistic regression", "Chance"))
ltype <- c("SL" = "solid", "Logistic regression" = "longdash", "Chance" = "dotted")

plot_sl_inclsusp<-eb_all %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(group=Method,colour=Method,linetype=Method)) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "gray")) +
  geom_ribbon(aes(ymin = X19, ymax = X20, group=Method), alpha = 0.1,linetype=0) +
  geom_point(aes(x=FourT.effort.inclsusp, y=FourT.benefit.inclsusp), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort.inclsusp, y=ThreeT.benefit.inclsusp), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort.inclsusp, y=TwoT.benefit.inclsusp), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort.inclsusp, y=OneT.benefit.inclsusp), colour="red", shape=3) +
  annotate(geom="text", x=0.6, y=0.5, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.6, y=0.45, label=paste("AUC(LR)=",round(subset(eb_all,Method=="Logistic regression")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=0.6, y=0.4, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance")$AUC[1],3),sep=""), hjust=0,
           color="gray",size=5) +
  annotate(geom="text", x=FourT.effort.inclsusp, y=FourT.benefit.inclsusp-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort.inclsusp, y=ThreeT.benefit.inclsusp+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort.inclsusp, y=TwoT.benefit.inclsusp, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort.inclsusp, y=OneT.benefit.inclsusp, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of actionable primary care contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D receiving alert during 90-day lead-up to diagnosis") +
  ggtitle("Validation (using CPRD/HES) of the SuperLearner algorithm (developed on SAIL): sensitivity analysis including the 1,022 with suspected T1D")


saveRDS(eb_sl,file = paste(path_to_SLobj,"/eb_sl.rds",sep = ""))
saveRDS(eb_sl_14,file = paste(path_to_SLobj,"/eb_sl_14.rds",sep = ""))
saveRDS(eb_sl_45,file = paste(path_to_SLobj,"/eb_sl_45.rds",sep = ""))
saveRDS(eb_sl_180,file = paste(path_to_SLobj,"/eb_sl_180.rds",sep = ""))
saveRDS(eb_sl_inclsusp,file = paste(path_to_SLobj,"/eb_sl_inclsusp.rds",sep = ""))
saveRDS(eb_glm,file = paste(path_to_SLobj,"/eb_glm.rds",sep = ""))
saveRDS(eb_glm_inclsusp,file = paste(path_to_SLobj,"/eb_glm_inclsusp.rds",sep = ""))
saveRDS(eb_chance1,file = paste(path_to_SLobj,"/eb_chance1.rds",sep = ""))
saveRDS(eb_chance1_14,file = paste(path_to_SLobj,"/eb_chance1_14.rds",sep = ""))
saveRDS(eb_chance1_45,file = paste(path_to_SLobj,"/eb_chance1_45.rds",sep = ""))
saveRDS(eb_chance1_180,file = paste(path_to_SLobj,"/eb_chance1_180.rds",sep = ""))
saveRDS(eb_chance1_inclsusp,file = paste(path_to_SLobj,"/eb_chance1_inclsusp.rds",sep = ""))

eb_sl<-readRDS(file = paste(path_to_SLobj,"/eb_sl.rds",sep = ""))
eb_sl_14<-readRDS(file = paste(path_to_SLobj,"/eb_sl_14.rds",sep = ""))
eb_sl_45<-readRDS(file = paste(path_to_SLobj,"/eb_sl_45.rds",sep = ""))
eb_sl_180<-readRDS(file = paste(path_to_SLobj,"/eb_sl_180.rds",sep = ""))
eb_sl_inclsusp<-readRDS(file = paste(path_to_SLobj,"/eb_sl_inclsusp.rds",sep = ""))
eb_glm<-readRDS(file = paste(path_to_SLobj,"/eb_glm.rds",sep = ""))
eb_glm_inclsusp<-readRDS(file = paste(path_to_SLobj,"/eb_glm_inclsusp.rds",sep = ""))
eb_chance1<-readRDS(file = paste(path_to_SLobj,"/eb_chance1.rds",sep = ""))
eb_chance1_14<-readRDS(file = paste(path_to_SLobj,"/eb_chance1_14.rds",sep = ""))
eb_chance1_45<-readRDS(file = paste(path_to_SLobj,"/eb_chance1_45.rds",sep = ""))
eb_chance1_180<-readRDS(file = paste(path_to_SLobj,"/eb_chance1_180.rds",sep = ""))
eb_chance1_inclsusp<-readRDS(file = paste(path_to_SLobj,"/eb_chance1_inclsusp.rds",sep = ""))


#MAKE RESULTS TABLES
row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

print(signif(100*eb_sl[row10,]$X2,3))
print(paste0("(",signif(100*eb_sl[row10,]$X19,3),", ",signif(100*eb_sl[row10,]$X20,3),")"))

print(signif(100*eb_sl[row5,]$X2,3))
print(paste0("(",signif(100*eb_sl[row5,]$X19,3),", ",signif(100*eb_sl[row5,]$X20,3),")"))

print(signif(100*eb_sl[row3p1,]$X2,3))
print(paste0("(",signif(100*eb_sl[row3p1,]$X19,3),", ",signif(100*eb_sl[row3p1,]$X20,3),")"))

row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

print(signif(100*eb_glm[row10,]$X2,3))
print(paste0("(",signif(100*eb_glm[row10,]$X19,3),", ",signif(100*eb_glm[row10,]$X20,3),")"))

print(signif(100*eb_glm[row5,]$X2,3))
print(paste0("(",signif(100*eb_glm[row5,]$X19,3),", ",signif(100*eb_glm[row5,]$X20,3),")"))

print(signif(100*eb_glm[row3p1,]$X2,3))
print(paste0("(",signif(100*eb_glm[row3p1,]$X19,3),", ",signif(100*eb_glm[row3p1,]$X20,3),")"))

row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

print(signif(100*eb_chance1[row10,]$X2,3))
print(paste0("(",signif(100*eb_chance1[row10,]$X19,3),", ",signif(100*eb_chance1[row10,]$X20,3),")"))

print(signif(100*eb_chance1[row5,]$X2,3))
print(paste0("(",signif(100*eb_chance1[row5,]$X19,3),", ",signif(100*eb_chance1[row5,]$X20,3),")"))

print(signif(100*eb_chance1[row3p1,]$X2,3))
print(paste0("(",signif(100*eb_chance1[row3p1,]$X19,3),", ",signif(100*eb_chance1[row3p1,]$X20,3),")"))

print(signif(100*OneT.benefit,3))
print(
  paste0(
    "(",
    signif((100*OneT.benefit-1.96*100*SE.OneT.benefit),3),
    ",",
    signif((100*OneT.benefit+1.96*100*SE.OneT.benefit),3),
    ")"
    )
  )


row10=which.min(as.data.table(eb_sl_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl_inclsusp)[X1>0.031][,X1])

print(signif(100*eb_sl_inclsusp[row10,]$X2,3))
print(paste0("(",signif(100*eb_sl_inclsusp[row10,]$X19,3),", ",signif(100*eb_sl_inclsusp[row10,]$X20,3),")"))

print(signif(100*eb_sl_inclsusp[row5,]$X2,3))
print(paste0("(",signif(100*eb_sl_inclsusp[row5,]$X19,3),", ",signif(100*eb_sl_inclsusp[row5,]$X20,3),")"))

print(signif(100*eb_sl_inclsusp[row3p1,]$X2,3))
print(paste0("(",signif(100*eb_sl_inclsusp[row3p1,]$X19,3),", ",signif(100*eb_sl_inclsusp[row3p1,]$X20,3),")"))

row10=which.min(as.data.table(eb_glm_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm_inclsusp)[X1>0.031][,X1])

print(signif(100*eb_glm_inclsusp[row10,]$X2,3))
print(paste0("(",signif(100*eb_glm_inclsusp[row10,]$X19,3),", ",signif(100*eb_glm_inclsusp[row10,]$X20,3),")"))

print(signif(100*eb_glm_inclsusp[row5,]$X2,3))
print(paste0("(",signif(100*eb_glm_inclsusp[row5,]$X19,3),", ",signif(100*eb_glm_inclsusp[row5,]$X20,3),")"))

print(signif(100*eb_glm_inclsusp[row3p1,]$X2,3))
print(paste0("(",signif(100*eb_glm_inclsusp[row3p1,]$X19,3),", ",signif(100*eb_glm_inclsusp[row3p1,]$X20,3),")"))


row10=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.031][,X1])

print(signif(100*eb_chance1_inclsusp[row10,]$X2,3))
print(paste0("(",signif(100*eb_chance1_inclsusp[row10,]$X19,3),", ",signif(100*eb_chance1_inclsusp[row10,]$X20,3),")"))

print(signif(100*eb_chance1_inclsusp[row5,]$X2,3))
print(paste0("(",signif(100*eb_chance1_inclsusp[row5,]$X19,3),", ",signif(100*eb_chance1_inclsusp[row5,]$X20,3),")"))

print(signif(100*eb_chance1_inclsusp[row3p1,]$X2,3))
print(paste0("(",signif(100*eb_chance1_inclsusp[row3p1,]$X19,3),", ",signif(100*eb_chance1_inclsusp[row3p1,]$X20,3),")"))

print(signif(100*OneT.benefit.inclsusp,3))
print(
  paste0(
    "(",
    signif((100*OneT.benefit.inclsusp-1.96*100*SE.OneT.benefit.inclsusp),3),
    ",",
    signif((100*OneT.benefit.inclsusp+1.96*100*SE.OneT.benefit.inclsusp),3),
    ")"
    )
  )







row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

print(signif(eb_sl[row10,]$X7,3))
print(paste0("(",signif(eb_sl[row10,]$X21,3),", ",signif(eb_sl[row10,]$X22,3),")"))

print(signif(eb_sl[row5,]$X7,3))
print(paste0("(",signif(eb_sl[row5,]$X21,3),", ",signif(eb_sl[row5,]$X22,3),")"))

print(signif(eb_sl[row3p1,]$X7,3))
print(paste0("(",signif(eb_sl[row3p1,]$X21,3),", ",signif(eb_sl[row3p1,]$X22,3),")"))

row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

print(signif(eb_glm[row10,]$X7,3))
print(paste0("(",signif(eb_glm[row10,]$X21,3),", ",signif(eb_glm[row10,]$X22,3),")"))

print(signif(eb_glm[row5,]$X7,3))
print(paste0("(",signif(eb_glm[row5,]$X21,3),", ",signif(eb_glm[row5,]$X22,3),")"))

print(signif(eb_glm[row3p1,]$X7,3))
print(paste0("(",signif(eb_glm[row3p1,]$X21,3),", ",signif(eb_glm[row3p1,]$X22,3),")"))

row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

print(signif(eb_chance1[row10,]$X7,3))
print(paste0("(",signif(eb_chance1[row10,]$X21,3),", ",signif(eb_chance1[row10,]$X22,3),")"))

print(signif(eb_chance1[row5,]$X7,3))
print(paste0("(",signif(eb_chance1[row5,]$X21,3),", ",signif(eb_chance1[row5,]$X22,3),")"))

print(signif(eb_chance1[row3p1,]$X7,3))
print(paste0("(",signif(eb_chance1[row3p1,]$X21,3),", ",signif(eb_chance1[row3p1,]$X22,3),")"))




row10=which.min(as.data.table(eb_sl_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl_inclsusp)[X1>0.031][,X1])

print(signif(eb_sl_inclsusp[row10,]$X7,3))
print(paste0("(",signif(eb_sl_inclsusp[row10,]$X21,3),", ",signif(eb_sl_inclsusp[row10,]$X22,3),")"))

print(signif(eb_sl_inclsusp[row5,]$X7,3))
print(paste0("(",signif(eb_sl_inclsusp[row5,]$X21,3),", ",signif(eb_sl_inclsusp[row5,]$X22,3),")"))

print(signif(eb_sl_inclsusp[row3p1,]$X7,3))
print(paste0("(",signif(eb_sl_inclsusp[row3p1,]$X21,3),", ",signif(eb_sl_inclsusp[row3p1,]$X22,3),")"))

row10=which.min(as.data.table(eb_glm_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm_inclsusp)[X1>0.031][,X1])

print(signif(eb_glm_inclsusp[row10,]$X7,3))
print(paste0("(",signif(eb_glm_inclsusp[row10,]$X21,3),", ",signif(eb_glm_inclsusp[row10,]$X22,3),")"))

print(signif(eb_glm_inclsusp[row5,]$X7,3))
print(paste0("(",signif(eb_glm_inclsusp[row5,]$X21,3),", ",signif(eb_glm_inclsusp[row5,]$X22,3),")"))

print(signif(eb_glm_inclsusp[row3p1,]$X7,3))
print(paste0("(",signif(eb_glm_inclsusp[row3p1,]$X21,3),", ",signif(eb_glm_inclsusp[row3p1,]$X22,3),")"))


row10=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.031][,X1])

print(signif(eb_chance1_inclsusp[row10,]$X7,3))
print(paste0("(",signif(eb_chance1_inclsusp[row10,]$X21,3),", ",signif(eb_chance1_inclsusp[row10,]$X22,3),")"))

print(signif(eb_chance1_inclsusp[row5,]$X7,3))
print(paste0("(",signif(eb_chance1_inclsusp[row5,]$X21,3),", ",signif(eb_chance1_inclsusp[row5,]$X22,3),")"))

print(signif(eb_chance1_inclsusp[row3p1,]$X7,3))
print(paste0("(",signif(eb_chance1_inclsusp[row3p1,]$X21,3),", ",signif(eb_chance1_inclsusp[row3p1,]$X22,3),")"))









row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

print(signif(eb_sl[row10,]$X6,3))
print(paste0("(",signif(eb_sl[row10,]$X23,3),", ",signif(eb_sl[row10,]$X24,3),")"))

print(signif(eb_sl[row5,]$X6,3))
print(paste0("(",signif(eb_sl[row5,]$X23,3),", ",signif(eb_sl[row5,]$X24,3),")"))

print(signif(eb_sl[row3p1,]$X6,3))
print(paste0("(",signif(eb_sl[row3p1,]$X23,3),", ",signif(eb_sl[row3p1,]$X24,3),")"))

row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

print(signif(eb_glm[row10,]$X6,3))
print(paste0("(",signif(eb_glm[row10,]$X23,3),", ",signif(eb_glm[row10,]$X24,3),")"))

print(signif(eb_glm[row5,]$X6,3))
print(paste0("(",signif(eb_glm[row5,]$X23,3),", ",signif(eb_glm[row5,]$X24,3),")"))

print(signif(eb_glm[row3p1,]$X6,3))
print(paste0("(",signif(eb_glm[row3p1,]$X23,3),", ",signif(eb_glm[row3p1,]$X24,3),")"))

row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

print(signif(eb_chance1[row10,]$X6,3))
print(paste0("(",signif(eb_chance1[row10,]$X23,3),", ",signif(eb_chance1[row10,]$X24,3),")"))

print(signif(eb_chance1[row5,]$X6,3))
print(paste0("(",signif(eb_chance1[row5,]$X23,3),", ",signif(eb_chance1[row5,]$X24,3),")"))

print(signif(eb_chance1[row3p1,]$X6,3))
print(paste0("(",signif(eb_chance1[row3p1,]$X23,3),", ",signif(eb_chance1[row3p1,]$X24,3),")"))




row10=which.min(as.data.table(eb_sl_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl_inclsusp)[X1>0.031][,X1])

print(signif(eb_sl_inclsusp[row10,]$X6,3))
print(paste0("(",signif(eb_sl_inclsusp[row10,]$X23,3),", ",signif(eb_sl_inclsusp[row10,]$X24,3),")"))

print(signif(eb_sl_inclsusp[row5,]$X6,3))
print(paste0("(",signif(eb_sl_inclsusp[row5,]$X23,3),", ",signif(eb_sl_inclsusp[row5,]$X24,3),")"))

print(signif(eb_sl_inclsusp[row3p1,]$X6,3))
print(paste0("(",signif(eb_sl_inclsusp[row3p1,]$X23,3),", ",signif(eb_sl_inclsusp[row3p1,]$X24,3),")"))

row10=which.min(as.data.table(eb_glm_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm_inclsusp)[X1>0.031][,X1])

print(signif(eb_glm_inclsusp[row10,]$X6,3))
print(paste0("(",signif(eb_glm_inclsusp[row10,]$X23,3),", ",signif(eb_glm_inclsusp[row10,]$X24,3),")"))

print(signif(eb_glm_inclsusp[row5,]$X6,3))
print(paste0("(",signif(eb_glm_inclsusp[row5,]$X23,3),", ",signif(eb_glm_inclsusp[row5,]$X24,3),")"))

print(signif(eb_glm_inclsusp[row3p1,]$X6,3))
print(paste0("(",signif(eb_glm_inclsusp[row3p1,]$X23,3),", ",signif(eb_glm_inclsusp[row3p1,]$X24,3),")"))


row10=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1_inclsusp)[X1>0.031][,X1])

print(signif(eb_chance1_inclsusp[row10,]$X6,3))
print(paste0("(",signif(eb_chance1_inclsusp[row10,]$X23,3),", ",signif(eb_chance1_inclsusp[row10,]$X24,3),")"))

print(signif(eb_chance1_inclsusp[row5,]$X6,3))
print(paste0("(",signif(eb_chance1_inclsusp[row5,]$X23,3),", ",signif(eb_chance1_inclsusp[row5,]$X24,3),")"))

print(signif(eb_chance1_inclsusp[row3p1,]$X6,3))
print(paste0("(",signif(eb_chance1_inclsusp[row3p1,]$X23,3),", ",signif(eb_chance1_inclsusp[row3p1,]$X24,3),")"))







row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))






row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))





row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & diagnosis_in_DKA==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))












row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))






row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))





row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_u6==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))














row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))






row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))





row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_7t12==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))











row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))






row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))





row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]

table=table(merged_cprd_small[EVENT_SEQN==1 & T1D==1 & AGE_AT_T1D_DIAG_13p==1][,caught_atall])
nt=table[1]+table[2]
pt=table[2]/nt
set=sqrt(pt*(1-pt)/nt)
llt=pt-set*1.96
ult=pt+set*1.96
print(signif(100*pt,3))
print(paste0("(",signif(100*llt,3),", ",signif(100*ult,3),")"))











row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))






row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))





row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & diagnosis_in_DKA==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))






row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))






row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))





row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_u6==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))












row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))






row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))





row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_7t12==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))













row10=which.min(as.data.table(eb_sl)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_sl)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_sl)[X1>0.031][,X1])

merged_cprd[,p_combined:=0.74832321*sl.p1d+0.03514735*sl.cp7d+0.13863583*sl.cp14d+0.03932865*sl.cp30d+0.03856492*sl.cp90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_sl[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))






row10=which.min(as.data.table(eb_glm)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_glm)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_glm)[X1>0.031][,X1])

merged_cprd[,p_combined:=glm.p366d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_glm[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))





row10=which.min(as.data.table(eb_chance1)[X1>0.1][,X1])
row5=which.min(as.data.table(eb_chance1)[X1>0.05][,X1])
row3p1=which.min(as.data.table(eb_chance1)[X1>0.031][,X1])

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE & check_timings==TRUE]
thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row10,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row5,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))


thresh=max(merged_cprd_small[,p_combined])*(eb_chance1[row3p1,]$X3)/10
merged_cprd_small[,caught_now:=(included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90]
merged_cprd_small[,caught_atall:=max(caught_now),by=new_id2]
merged_cprd_small[,antic_now:=ifelse((included_now==TRUE) & (p_combined>=thresh) & nont1==FALSE & time_until_diagnosis<=90,time_until_diagnosis,0)]
merged_cprd_small[,antic_max:=max(antic_now),by=new_id2]

mt=mean(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
sdt=sd(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,antic_max],na.rm=TRUE)
nt=sum(merged_cprd_small[EVENT_SEQN==1 & caught_atall==1 & AGE_AT_T1D_DIAG_13p==1][,EVENT_SEQN],na.rm=TRUE)
llt=mt-1.96*sdt/sqrt(nt)
ult=mt+1.96*sdt/sqrt(nt)

print(signif(mt,3))
print(paste0("(",signif(llt,3),", ",signif(ult,3),")"))

```


```{r performance-evaluation-2b}
merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
merged_cprd_small<-merged_cprd_small[permitted==1 & duplicate==0 & included1==1 & included2==1 & included3==1 & included4==1 & included5==1 & susp_t1d_no_conf_in_diag_date==FALSE]
eb_chance<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

eb_sl[[1]]<-cbind(eb_sl[[1]],eb_sl[[1]][,2]-1.96*eb_sl[[1]][,18],eb_sl[[1]][,2]+1.96*eb_sl[[1]][,18])
eb_glm[[1]]<-cbind(eb_glm[[1]],eb_glm[[1]][,2]-1.96*eb_glm[[1]][,18],eb_glm[[1]][,2]+1.96*eb_glm[[1]][,18])
plot(eb_sl[[1]][,1],eb_sl[[1]][,2],type="s")
points(eb_sl[[1]][,1],eb_sl[[1]][,19],type="s",col="gray")
points(eb_sl[[1]][,1],eb_sl[[1]][,20],type="s",col="gray")
points(eb_glm[[1]][,1],eb_glm[[1]][,2],type="s")
points(eb_glm[[1]][,1],eb_glm[[1]][,19],type="s",col="gray")
points(eb_glm[[1]][,1],eb_glm[[1]][,20],type="s",col="gray")
points(eb_chance[[1]][,1],eb_chance[[1]][,2],type="s",col="1")
```

```{r performance-evaluation-3}
merged_cprd[,p_combined:=sl.p180d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl180<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

merged_cprd[,p_combined:=sl.p90d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl90<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

merged_cprd[,p_combined:=sl.p30d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl30<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

merged_cprd[,p_combined:=sl.p14d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl14<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

merged_cprd[,p_combined:=sl.p7d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl7<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)

merged_cprd[,p_combined:=sl.p1d]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl1<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
```

```{r performance-evaluation-4}
merged_cprd[,p_combined:=0.3208263*sl.p1d.t+0.1493042*sl.cp7d.t+0.2527947*sl.cp14d.t+0.1003377*sl.cp30d.t+0.09838923*sl.cp90d.t]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_slopt<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
```


```{r performance-evaluation-5}
merged_cprd[,p_combined:=0.3208263*p1d+0.1493042*cp7d+0.2527947*cp14d+0.1003377*cp30d+0.09838923*cp90d]
merged_cprd[,SLp:=p_combined]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
plot(eb_sl[[1]][,1],eb_sl[[1]][,2])

merged_consultations_small<-merged_consultations[,.(new_id2,eventdate,totalCOTs)]
rm(merged_consultations)
setnames(merged_consultations_small,"eventdate","EVENT_DT")

setkey(merged_cprd,new_id2,EVENT_DT)
setkey(merged_consultations_small,new_id2,EVENT_DT)
final_cprd<-merge(merged_cprd,merged_consultations_small)

final_cprd_small<-final_cprd[T1D==1 | su<0.0025]
eb_sl_rest<-eb.calc(final_cprd_small,wind_days=90,cutoff=1)
plot(eb_sl_rest[[1]][,1],eb_sl_rest[[1]][,2])


NOTIMING_p1d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOTIMING_p1d_all.rds",sep = ""))
NOTIMING_p7d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOTIMING_p7d_all.rds",sep = ""))
NOTIMING_p14d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOTIMING_p14d_all.rds",sep = ""))
NOTIMING_p30d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOTIMING_p30d_all.rds",sep = ""))
NOTIMING_p90d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOTIMING_p90d_all.rds",sep = ""))
NOTIMING_p180d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOTIMING_p180d_all.rds",sep = ""))
NOTIMING_p366d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOTIMING_p366d_all.rds",sep = ""))

NOLAGS_p1d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOLAGS_p1d_all.rds",sep = ""))
NOLAGS_p7d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOLAGS_p7d_all.rds",sep = ""))
NOLAGS_p14d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOLAGS_p14d_all.rds",sep = ""))
NOLAGS_p30d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOLAGS_p30d_all.rds",sep = ""))
NOLAGS_p90d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOLAGS_p90d_all.rds",sep = ""))
NOLAGS_p180d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOLAGS_p180d_all.rds",sep = ""))
NOLAGS_p366d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOLAGS_p366d_all.rds",sep = ""))

NODEMO_p1d<-readRDS(file = paste(path_to_SLobj,"/v2022_NODEMO_p1d_all.rds",sep = ""))
NODEMO_p7d<-readRDS(file = paste(path_to_SLobj,"/v2022_NODEMO_p7d_all.rds",sep = ""))
NODEMO_p14d<-readRDS(file = paste(path_to_SLobj,"/v2022_NODEMO_p14d_all.rds",sep = ""))
NODEMO_p30d<-readRDS(file = paste(path_to_SLobj,"/v2022_NODEMO_p30d_all.rds",sep = ""))
NODEMO_p90d<-readRDS(file = paste(path_to_SLobj,"/v2022_NODEMO_p90d_all.rds",sep = ""))
NODEMO_p180d<-readRDS(file = paste(path_to_SLobj,"/v2022_NODEMO_p180d_all.rds",sep = ""))
NODEMO_p366d<-readRDS(file = paste(path_to_SLobj,"/v2022_NODEMO_p366d_all.rds",sep = ""))

NOOTHER_p1d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOOTHER_p1d_all.rds",sep = ""))
NOOTHER_p7d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOOTHER_p7d_all.rds",sep = ""))
NOOTHER_p14d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOOTHER_p14d_all.rds",sep = ""))
NOOTHER_p30d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOOTHER_p30d_all.rds",sep = ""))
NOOTHER_p90d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOOTHER_p90d_all.rds",sep = ""))
NOOTHER_p180d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOOTHER_p180d_all.rds",sep = ""))
NOOTHER_p366d<-readRDS(file = paste(path_to_SLobj,"/v2022_NOOTHER_p366d_all.rds",sep = ""))

NO4T_p1d<-readRDS(file = paste(path_to_SLobj,"/v2022_NO4T_p1d_all.rds",sep = ""))
NO4T_p7d<-readRDS(file = paste(path_to_SLobj,"/v2022_NO4T_p7d_all.rds",sep = ""))
NO4T_p14d<-readRDS(file = paste(path_to_SLobj,"/v2022_NO4T_p14d_all.rds",sep = ""))
NO4T_p30d<-readRDS(file = paste(path_to_SLobj,"/v2022_NO4T_p30d_all.rds",sep = ""))
NO4T_p90d<-readRDS(file = paste(path_to_SLobj,"/v2022_NO4T_p90d_all.rds",sep = ""))
NO4T_p180d<-readRDS(file = paste(path_to_SLobj,"/v2022_NO4T_p180d_all.rds",sep = ""))
NO4T_p366d<-readRDS(file = paste(path_to_SLobj,"/v2022_NO4T_p366d_all.rds",sep = ""))


merged_cprd[,t1d:=is.na(t1d_diag_dt)==FALSE]
merged_cprd[,SLp:=p1d+(1-p1d)*p7d+(1-p1d)*(1-p7d)*p14d+(1-p1d)*(1-p7d)*(1-p14d)*p30d+(1-p1d)*(1-p7d)*(1-p14d)*(1-p30d)*p90d+(1-p1d)*(1-p7d)*(1-p14d)*(1-p30d)*(1-p90d)*p180d+(1-p1d)*(1-p7d)*(1-p14d)*(1-p30d)*(1-p90d)*(1-p180d)*p366d]
merged_cprd[,SLp_14:=p1d+(1-p1d)*p7d+(1-p1d)*(1-p7d)*p14d]

##########NEEDS CHANGING:
merged_cprd[,NOTIMING_SLp:=NOTIMING_p1d+(1-NOTIMING_p1d)*NOTIMING_p7d+(1-NOTIMING_p1d)*(1-NOTIMING_p7d)*NOTIMING_p14d+(1-NOTIMING_p1d)*(1-NOTIMING_p7d)*(1-NOTIMING_p14d)*NOTIMING_p30d]
merged_cprd[,NOLAGS_SLp:=NOLAGS_p1d+(1-NOLAGS_p1d)*NOLAGS_p7d+(1-NOLAGS_p1d)*(1-NOLAGS_p7d)*NOLAGS_p14d+(1-NOLAGS_p1d)*(1-NOLAGS_p7d)*(1-NOLAGS_p14d)*NOLAGS_p30d]
merged_cprd[,NODEMO_SLp:=NODEMO_p1d+(1-NODEMO_p1d)*NODEMO_p7d+(1-NODEMO_p1d)*(1-NODEMO_p7d)*NODEMO_p14d+(1-NODEMO_p1d)*(1-NODEMO_p7d)*(1-NODEMO_p14d)*NODEMO_p30d]
merged_cprd[,NOOTHER_SLp:=NOOTHER_p1d+(1-NOOTHER_p1d)*NOOTHER_p7d+(1-NOOTHER_p1d)*(1-NOOTHER_p7d)*NOOTHER_p14d+(1-NOOTHER_p1d)*(1-NOOTHER_p7d)*(1-NOOTHER_p14d)*NOOTHER_p30d]
merged_cprd[,NO4T_SLp:=NO4T_p1d+(1-NO4T_p1d)*NO4T_p7d+(1-NO4T_p1d)*(1-NO4T_p7d)*NO4T_p14d+(1-NO4T_p1d)*(1-NO4T_p7d)*(1-NO4T_p14d)*NO4T_p30d]

merged_cprd[EVENT_SEQN==1][,table(is.na(t1d_diag_dt)==FALSE)]

merged_cprd<-merged_cprd[susp_t1d_no_conf_in_diag_date==FALSE]

merged_cprd[EVENT_SEQN==1][,table(is.na(t1d_diag_dt)==FALSE)]



#create data.table of just T1Ds to create the graphs
T1Ds<-copy(final_cprd)
T1Ds<-T1Ds[t1d==TRUE]
T1Ds<-T1Ds[,c("EVENT_DT","GNDR_CD","t1d_diag_dt","new_id2","time_until_diagnosis","AGE_AT_EVT_days","AGE_AT_T1D_DIAG","EVENT_SEQN","diagnosis_in_DKA","SLp")]
T1Ds[,orig_order:=1:nrow(T1Ds)]
setorder(T1Ds,'AGE_AT_T1D_DIAG')
T1Ds[,new_order:=1:nrow(T1Ds)]
setorder(T1Ds,'EVENT_SEQN')
T1Ds[,patient_order:=1:nrow(T1Ds)]
order_key_dt<-T1Ds[EVENT_SEQN==1,c('new_id2','patient_order')]
T1Ds[,patient_order:=NULL]
T1Ds<-merge(T1Ds,order_key_dt,by='new_id2')
setorder(T1Ds,'patient_order')

#which are the consultations that would be flagged by the algorithm at the "10% of consultations" threshold?
T1Ds[,flag_10:=SLp>=0.027]
T1Ds[,flag_10_rev:=SLp<0.027]

T1Ds[,alert_prop:=SLp<0.027,by=time_until_diagnosis]

prop_table<-matrix(NA,nrow=366,ncol=2)
for (i in 0:365) {
  j=i+1
  prop_table[j,1]<-i
  prop_table[j,2]<-prop.table(table(T1Ds[time_until_diagnosis==i][,flag_10]))[2]
}

T1Ds[,lw_all:=loess(flag_10~time_until_diagnosis, data=T1Ds, span=0.1)$fitted] 
T1Ds[,lw_all:=ifelse(time_until_diagnosis>0,lw_all,prop_table[1,2])] 

plot_prop1<-T1Ds %>% 
  ggplot(aes(x=time_until_diagnosis,y=lw_all)) +
  geom_point(size=.5,color='black') +
  scale_x_reverse() +
  theme_ipsum() +
  theme(legend.position="none", axis.title.y = element_text(size=12,hjust=0.5), axis.title.x = element_blank(), plot.title = element_text(size=18), axis.text.x = element_blank(), axis.text.y = element_text(size=8), plot.margin = margin(b=0)) +
  xlab("Days until diagnosis") +
  ylab("Proportion alerted") +
  ggtitle("Contact alerts for T1D patients prior to diagnosis")

plot_prop2<-T1Ds %>% 
  ggplot(aes(x=time_until_diagnosis,y=lw_all)) +
  geom_point(size=.5,color='black') +
  xlim(365,0) +
  theme_ipsum() +
  theme(legend.position="none", axis.title.y = element_text(size=12,hjust=0.5), axis.title.x = element_blank(), plot.title = element_text(size=18), axis.text.x = element_blank(), axis.text.y = element_text(size=8,hjust=0.5), plot.margin = margin(b=0)) +
  xlab("Days until diagnosis") +
  ylab("Proportion alerted") +
  ggtitle("Contact alerts for T1D patients prior to diagnosis: 1 year before diagnosis")

plot_prop3<-T1Ds %>% 
  ggplot(aes(x=time_until_diagnosis,y=lw_all)) +
  geom_point(size=.5,color='black') +
  xlim(42,0) +
  theme_ipsum() +
  theme(legend.position="none", axis.title.y = element_text(size=12,hjust=0.5), axis.title.x = element_blank(), plot.title = element_text(size=18), axis.text.x = element_blank(), axis.text.y = element_text(size=8,hjust=0.5), plot.margin = margin(b=0)) +
  xlab("Days until diagnosis") +
  ylab("Proportion alerted") +
  ggtitle("Contact alerts for T1D patients prior to diagnosis: 42 days before diagnosis")

plot1<-T1Ds  %>%
  ggplot( aes(x=time_until_diagnosis, y=patient_order, colour=flag_10_rev)) +
  geom_point(size=0.5,shape=15) +
  scale_x_reverse() +
  scale_y_reverse() +
  theme_ipsum() +
  theme(axis.title.x = element_text(size=12,hjust=0.5), legend.position="none", axis.ticks.y = element_blank(), axis.text.y = element_blank(), plot.title = element_blank(), plot.caption = element_text(hjust=0,size=14), plot.margin=margin(t=0,l=11.9)) +
  xlab("Days until diagnosis") +
  ylab("")  +
  labs(caption="Notes: \n 1. Each line is a patient, ordered by age at diagnosis (youngest at the top). \n 2. Each point is a contact. Red points correspond to contacts in which an alert would have occurred. \n 3. This is based on using the SuperLearner algorithm with a threshold that leads to an alert in 10% of contacts with a patient under 15 yo.") 

plot2<-T1Ds  %>%
  ggplot( aes(x=time_until_diagnosis, y=patient_order, colour=flag_10_rev)) +
  geom_point(size=1,shape=15) +
  xlim(365,0) +
  scale_y_reverse() +
  theme_ipsum() +
  theme(axis.title.x = element_text(size=12,hjust=0.5), legend.position="none", axis.ticks.y = element_blank(), axis.text.y = element_blank(), plot.title = element_blank(), plot.caption = element_text(hjust=0,size=14), plot.margin=margin(t=0,l=11.9)) +
  xlab("Days until diagnosis") +
  ylab("")  +
  labs(caption="Notes: \n 1. Each line is a patient, ordered by age at diagnosis (youngest at the top). \n 2. Each point is a contact. Red points correspond to contacts in which an alert would have occurred. \n 3. This is based on using the SuperLearner algorithm with a threshold that leads to an alert in 10% of contacts with a patient under 15 yo.") 

plot3<-T1Ds  %>%
  ggplot( aes(x=time_until_diagnosis, y=patient_order, colour=flag_10_rev)) +
  geom_point(size=1.5,shape=15) +
  xlim(42,0) +
  scale_y_reverse() +
  theme_ipsum() +
  theme(axis.title.x = element_text(size=12,hjust=0.5), legend.position="none", axis.ticks.y = element_blank(), axis.text.y = element_blank(), plot.title = element_blank(), plot.caption = element_text(hjust=0,size=14), plot.margin=margin(t=0,l=11.9)) +
  xlab("Days until diagnosis") +
  ylab("")  +
  labs(caption="Notes: \n 1. Each line is a patient, ordered by age at diagnosis (youngest at the top). \n 2. Each point is a contact. Red points correspond to contacts in which an alert would have occurred. \n 3. This is based on using the SuperLearner algorithm with a threshold that leads to an alert in 10% of contacts with a patient under 15 yo.") 

library("gridExtra")
grid.arrange(plot_prop1, plot1, ncol = 1, heights = c(1, 4))
grid.arrange(plot_prop2, plot2, ncol = 1, heights = c(1, 4))
grid.arrange(plot_prop3, plot3, ncol = 1, heights = c(1, 4))










#now, for comparison, do the same for some non T1Ds, with a fake diagnosis date for each
setorder(T1Ds,'orig_order')
ages<-as.data.table(T1Ds[EVENT_SEQN==1][,AGE_AT_T1D_DIAG])

nonT1Ds<-copy(final_cprd)
nonT1Ds<-nonT1Ds[t1d==FALSE]
nonT1Ds<-nonT1Ds[,c("EVENT_DT","GNDR_CD","t1d_diag_dt","new_id2","time_until_diagnosis","AGE_AT_EVT_days","AGE_AT_T1D_DIAG","EVENT_SEQN","diagnosis_in_DKA","SLp")]
nonT1Ds[,ru:=runif(1),by=new_id2]
nonT1Ds_small<-copy(nonT1Ds)
nonT1Ds_small<-nonT1Ds_small[ru<=0.000999]
ages[,new_id2:=nonT1Ds_small[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small<-merge(nonT1Ds_small,ages,by='new_id2')
nonT1Ds_small[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])

nonT1Ds_small_2<-copy(nonT1Ds)
nonT1Ds_small_2<-nonT1Ds_small_2[ru>0.000999 & ru<=0.0012445]
ages[,new_id2:=nonT1Ds_small_2[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small_2<-merge(nonT1Ds_small_2,ages,by='new_id2')
nonT1Ds_small_2[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small_2[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small_2[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small_2[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])

nonT1Ds_small_3<-copy(nonT1Ds)
nonT1Ds_small_3<-nonT1Ds_small_3[ru>0.0012445 & ru<=0.0013244]
ages[,new_id2:=nonT1Ds_small_3[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small_3<-merge(nonT1Ds_small_3,ages,by='new_id2')
nonT1Ds_small_3[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small_3[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small_3[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small_3[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])


nonT1Ds_small_4<-copy(nonT1Ds)
nonT1Ds_small_4<-nonT1Ds_small_4[ru>0.0013244 & ru<=0.001362]
ages[,new_id2:=nonT1Ds_small_4[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small_4<-merge(nonT1Ds_small_4,ages,by='new_id2')
nonT1Ds_small_4[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small_4[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small_4[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small_4[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])


nonT1Ds_small_5<-copy(nonT1Ds)
nonT1Ds_small_5<-nonT1Ds_small_5[ru>0.001362 & ru<=0.00138]
ages[,new_id2:=nonT1Ds_small_5[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small_5<-merge(nonT1Ds_small_5,ages,by='new_id2')
nonT1Ds_small_5[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small_5[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small_5[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small_5[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])

nonT1Ds_small_6<-copy(nonT1Ds)
nonT1Ds_small_6<-nonT1Ds_small_6[ru>0.00138 & ru<=0.0013895]
ages[,new_id2:=nonT1Ds_small_6[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small_6<-merge(nonT1Ds_small_6,ages,by='new_id2')
nonT1Ds_small_6[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small_6[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small_6[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small_6[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])

nonT1Ds_small_7<-copy(nonT1Ds)
nonT1Ds_small_7<-nonT1Ds_small_7[ru>0.0013895 & ru<=0.0013928]
ages[,new_id2:=nonT1Ds_small_7[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small_7<-merge(nonT1Ds_small_7,ages,by='new_id2')
nonT1Ds_small_7[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small_7[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small_7[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small_7[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])

nonT1Ds_small_8<-copy(nonT1Ds)
nonT1Ds_small_8<-nonT1Ds_small_8[ru>0.0013928 & ru<=0.0013978]
ages[,new_id2:=nonT1Ds_small_8[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small_8<-merge(nonT1Ds_small_8,ages,by='new_id2')
nonT1Ds_small_8[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small_8[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small_8[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small_8[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])


nonT1Ds_small_9<-copy(nonT1Ds)
nonT1Ds_small_9<-nonT1Ds_small_9[ru>0.0013978 & ru<=0.001402]
ages[,new_id2:=nonT1Ds_small_9[EVENT_SEQN==1][,new_id2]]
colnames(ages)<-c("AGE_AT_T1D_DIAG","new_id2")
nonT1Ds_small_9<-merge(nonT1Ds_small_9,ages,by='new_id2')
nonT1Ds_small_9[, check_timings:=AGE_AT_EVT_days<=AGE_AT_T1D_DIAG.y*365.25]
nonT1Ds_small_9[, check_timings_max:=max(check_timings),by=new_id2]
nonT1Ds_small_9[EVENT_SEQN==1][, table(check_timings_max)]
ages<-as.data.table(nonT1Ds_small_9[EVENT_SEQN==1][check_timings_max==0][,AGE_AT_T1D_DIAG.y])


nonT1Ds_final<-as.data.table(rbind(nonT1Ds_small,nonT1Ds_small_2,nonT1Ds_small_3,nonT1Ds_small_4,nonT1Ds_small_5,nonT1Ds_small_6,nonT1Ds_small_7,nonT1Ds_small_8,nonT1Ds_small_9))
nonT1Ds_final<-nonT1Ds_final[check_timings==1]
nonT1Ds<-nonT1Ds_final

nonT1Ds[,orig_order:=1:nrow(nonT1Ds)]
setorder(nonT1Ds,'AGE_AT_T1D_DIAG.y')
nonT1Ds[,new_order:=1:nrow(nonT1Ds)]
setorder(nonT1Ds,'EVENT_SEQN')
nonT1Ds[,patient_order:=1:nrow(nonT1Ds)]
order_key_dt<-nonT1Ds[EVENT_SEQN==1,c('new_id2','patient_order')]
nonT1Ds[,patient_order:=NULL]
nonT1Ds<-merge(nonT1Ds,order_key_dt,by='new_id2')
setorder(nonT1Ds,'patient_order')

#which are the consultations that would be flagged by the algorithm at the "10% of consultations" threshold?
nonT1Ds[,flag_10:=SLp>=0.027]
nonT1Ds[,flag_10_rev:=SLp<0.027]

nonT1Ds[,time_until_diagnosis:=round(AGE_AT_T1D_DIAG.y*365.25-AGE_AT_EVT_days,1)]
nonT1Ds[,alert_prop:=SLp<0.027,by=time_until_diagnosis]

prop_table<-matrix(NA,nrow=366,ncol=2)
for (i in 0:365) {
  j=i+1
  prop_table[j,1]<-i
  prop_table[j,2]<-prop.table(table(nonT1Ds[time_until_diagnosis==i][,flag_10]))[2]
}

nonT1Ds[,lw_all:=loess(flag_10~time_until_diagnosis, data=nonT1Ds, span=0.1)$fitted] 

plot_prop1<-nonT1Ds %>% 
  ggplot(aes(x=time_until_diagnosis,y=lw_all)) +
  geom_point(size=.5,color='black') +
  scale_x_reverse() +
  theme_ipsum() +
  theme(legend.position="none", axis.title.y = element_text(size=12,hjust=0.5), axis.title.x = element_blank(), plot.title = element_text(size=18), axis.text.x = element_blank(), axis.text.y = element_text(size=8), plot.margin = margin(b=0)) +
  xlab("Days until fake diagnosis") +
  ylab("Proportion alerted") +
  ggtitle("Contact alerts for non-T1D patients prior to fake diagnosis")

plot_prop2<-nonT1Ds %>% 
  ggplot(aes(x=time_until_diagnosis,y=lw_all)) +
  geom_point(size=.5,color='black') +
  xlim(365,0) +
  theme_ipsum() +
  theme(legend.position="none", axis.title.y = element_text(size=12,hjust=0.5), axis.title.x = element_blank(), plot.title = element_text(size=18), axis.text.x = element_blank(), axis.text.y = element_text(size=8,hjust=0.5), plot.margin = margin(b=0)) +
  xlab("Days until fake diagnosis") +
  ylab("Proportion alerted") +
  ggtitle("Contact alerts for non-T1D patients prior to fake diagnosis: 1 year before fake diagnosis")

plot_prop3<-nonT1Ds %>% 
  ggplot(aes(x=time_until_diagnosis,y=lw_all)) +
  geom_point(size=.5,color='black') +
  xlim(42,0) +
  theme_ipsum() +
  theme(legend.position="none", axis.title.y = element_text(size=12,hjust=0.5), axis.title.x = element_blank(), plot.title = element_text(size=18), axis.text.x = element_blank(), axis.text.y = element_text(size=8,hjust=0.5), plot.margin = margin(b=0)) +
  xlab("Days until fake diagnosis") +
  ylab("Proportion alerted") +
  ggtitle("Contact alerts for non-T1D patients prior to fake diagnosis: 42 days before fake diagnosis")

plot1<-nonT1Ds  %>%
  ggplot( aes(x=time_until_diagnosis, y=patient_order, colour=flag_10_rev)) +
  geom_point(size=0.5,shape=15) +
  scale_x_reverse() +
  scale_y_reverse() +
  theme_ipsum() +
  theme(axis.title.x = element_text(size=12,hjust=0.5), legend.position="none", axis.ticks.y = element_blank(), axis.text.y = element_blank(), plot.title = element_blank(), plot.caption = element_text(hjust=0,size=14), plot.margin=margin(t=0,l=15.5)) +
  xlab("Days until fake diagnosis") +
  ylab("")  +
  labs(caption="Notes: \n 1. Each line is a patient, ordered by age at fake diagnosis (youngest at the top). \n 2. Each point is a contact. Red points correspond to contacts in which an alert would have occurred. \n 3. This is based on using the SuperLearner algorithm with a threshold that leads to an alert in 10% of contacts with a patient under 15 yo.") 

plot2<-nonT1Ds  %>%
  ggplot( aes(x=time_until_diagnosis, y=patient_order, colour=flag_10_rev)) +
  geom_point(size=1,shape=15) +
  xlim(365,0) +
  scale_y_reverse() +
  theme_ipsum() +
  theme(axis.title.x = element_text(size=12,hjust=0.5), legend.position="none", axis.ticks.y = element_blank(), axis.text.y = element_blank(), plot.title = element_blank(), plot.caption = element_text(hjust=0,size=14), plot.margin=margin(t=0,l=15.5)) +
  xlab("Days until fake diagnosis") +
  ylab("")  +
  labs(caption="Notes: \n 1. Each line is a patient, ordered by age at fake diagnosis (youngest at the top). \n 2. Each point is a contact. Red points correspond to contacts in which an alert would have occurred. \n 3. This is based on using the SuperLearner algorithm with a threshold that leads to an alert in 10% of contacts with a patient under 15 yo.") 

plot3<-nonT1Ds  %>%
  ggplot( aes(x=time_until_diagnosis, y=patient_order, colour=flag_10_rev)) +
  geom_point(size=1.5,shape=15) +
  xlim(42,0) +
  scale_y_reverse() +
  theme_ipsum() +
  theme(axis.title.x = element_text(size=12,hjust=0.5), legend.position="none", axis.ticks.y = element_blank(), axis.text.y = element_blank(), plot.title = element_blank(), plot.caption = element_text(hjust=0,size=14), plot.margin=margin(t=0,l=15.5)) +
  xlab("Days until fake diagnosis") +
  ylab("")  +
  labs(caption="Notes: \n 1. Each line is a patient, ordered by age at fake diagnosis (youngest at the top). \n 2. Each point is a contact. Red points correspond to contacts in which an alert would have occurred. \n 3. This is based on using the SuperLearner algorithm with a threshold that leads to an alert in 10% of contacts with a patient under 15 yo.") 


grid.arrange(plot_prop1, plot1, ncol = 1, heights = c(1, 4))
grid.arrange(plot_prop2, plot2, ncol = 1, heights = c(1, 4))
grid.arrange(plot_prop3, plot3, ncol = 1, heights = c(1, 4))












merged_cprd[,p_combined:=SLp]
merged_cprd[,T1D:=as.numeric(t1d)]
merged_cprd[,ALF_PE:=new_id2]

prevalence_table<-merged_cprd[EVENT_SEQN==1][, .N, by=T1D]
prev<-prevalence_table[2,N]/(prevalence_table[1,N]+prevalence_table[2,N])

merged_cprd[,su:=runif(1),by=new_id2]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]

final_cprd_small<-final_cprd[T1D==1 | su<0.0025]
eb_sl<-eb.calc(final_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_sl,file = paste(path_to_SLobj,"eb_sl.rds",sep = ""))

merged_cprd[,p_combined:=glm.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_glm<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_glm,file = paste(path_to_SLobj,"eb_glm.rds",sep = ""))


merged_cprd[,p_combined:=NOTIMING_SLp]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_NOTIMING_sl<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_NOTIMING_sl,file = paste(path_to_SLobj,"eb_NOTIMING_sl.rds",sep = ""))

merged_cprd[,p_combined:=NOLAGS_SLp]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_NOLAGS_sl<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_NOLAGS_sl,file = paste(path_to_SLobj,"eb_NOLAGS_sl.rds",sep = ""))

merged_cprd[,p_combined:=NODEMO_SLp]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_NODEMO_sl<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_NODEMO_sl,file = paste(path_to_SLobj,"eb_NODEMO_sl.rds",sep = ""))

merged_cprd[,p_combined:=NOOTHER_SLp]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_NOOTHER_sl<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_NOOTHER_sl,file = paste(path_to_SLobj,"eb_NOOTHER_sl.rds",sep = ""))

merged_cprd[,p_combined:=NO4T_SLp]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_NO4T_sl<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_NO4T_sl,file = paste(path_to_SLobj,"eb_NO4T_sl.rds",sep = ""))

final_cprd[,p_combined:=chance1.p]
final_cprd_small<-final_cprd[T1D==1 | su<0.0025]
eb_chance1<-eb.calc(final_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance1,file = paste(path_to_SLobj,"eb_chance1.rds",sep = ""))

merged_cprd[,p_combined:=chance2.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance2<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance2,file = paste(path_to_SLobj,"eb_chance2.rds",sep = ""))

merged_cprd[,p_combined:=chance3.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance3<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance3,file = paste(path_to_SLobj,"eb_chance3.rds",sep = ""))

merged_cprd[,p_combined:=chance4.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance4<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance4,file = paste(path_to_SLobj,"eb_chance4.rds",sep = ""))

merged_cprd[,p_combined:=chance5.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance5<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance5,file = paste(path_to_SLobj,"eb_chance5.rds",sep = ""))

merged_cprd[,p_combined:=chance6.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance6<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance6,file = paste(path_to_SLobj,"eb_chance6.rds",sep = ""))

merged_cprd[,p_combined:=chance7.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance7<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance7,file = paste(path_to_SLobj,"eb_chance7.rds",sep = ""))

merged_cprd[,p_combined:=chance8.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance8<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance8,file = paste(path_to_SLobj,"eb_chance8.rds",sep = ""))

merged_cprd[,p_combined:=chance9.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance9<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance9,file = paste(path_to_SLobj,"eb_chance9.rds",sep = ""))

merged_cprd[,p_combined:=chance10.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance10<-eb.calc(merged_cprd_small,wind_days=90,cutoff=1)
saveRDS(eb_chance10,file = paste(path_to_SLobj,"eb_chance10.rds",sep = ""))

merged_cprd[,p_combined:=SLp]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl_45<-eb.calc(merged_cprd_small,wind_days=45,cutoff=1)
saveRDS(eb_sl_45,file = paste(path_to_SLobj,"eb_sl_45.rds",sep = ""))

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance1_45<-eb.calc(merged_cprd_small,wind_days=45,cutoff=1)
saveRDS(eb_chance1_45,file = paste(path_to_SLobj,"eb_chance1_45.rds",sep = ""))

merged_cprd[,p_combined:=SLp]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_sl_14<-eb.calc(merged_cprd_small,wind_days=14,cutoff=1)
saveRDS(eb_sl_14,file = paste(path_to_SLobj,"eb_sl_14.rds",sep = ""))

merged_cprd[,p_combined:=chance1.p]
merged_cprd_small<-merged_cprd[T1D==1 | su<0.001]
eb_chance1_14<-eb.calc(merged_cprd_small,wind_days=14,cutoff=1)
saveRDS(eb_chance1_14,file = paste(path_to_SLobj,"eb_chance1_14.rds",sep = ""))



eb_sl<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_sl.rds",sep = "")))
eb_sl_45<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_sl_45.rds",sep = "")))
eb_sl_14<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_sl_14.rds",sep = "")))
eb_glm<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_glm.rds",sep = "")))
eb_NOTIMING_sl<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_NOTIMING_sl.rds",sep = "")))
eb_NOLAGS_sl<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_NOLAGS_sl.rds",sep = "")))
eb_NODEMO_sl<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_NODEMO_sl.rds",sep = "")))
eb_NOOTHER_sl<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_NOOTHER_sl.rds",sep = "")))
eb_NO4T_sl<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_NO4T_sl.rds",sep = "")))
eb_chance1<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance1.rds",sep = "")))
eb_chance1_45<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance1_45.rds",sep = "")))
eb_chance1_14<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance1_14.rds",sep = "")))
eb_chance2<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance2.rds",sep = "")))
eb_chance3<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance3.rds",sep = "")))
eb_chance4<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance4.rds",sep = "")))
eb_chance5<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance5.rds",sep = "")))
eb_chance6<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance6.rds",sep = "")))
eb_chance7<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance7.rds",sep = "")))
eb_chance8<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance8.rds",sep = "")))
eb_chance9<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance9.rds",sep = "")))
eb_chance10<-as.data.frame(readRDS(file = paste(path_to_SLobj,"eb_chance10.rds",sep = "")))

eb_sl$Method="SL"
eb_glm$Method="Logistic regression"
eb_NOTIMING_sl$Method="SL - without timing"
eb_NOLAGS_sl$Method="SL - without lags"
eb_NODEMO_sl$Method="SL - without age/sex"
eb_NOOTHER_sl$Method="SL - without non-4T flags"
eb_NO4T_sl$Method="SL - without 4Ts"
eb_chance1$Method="Chance (1)"
eb_chance2$Method="Chance (2)"
eb_chance3$Method="Chance (3)"
eb_chance4$Method="Chance (4)"
eb_chance5$Method="Chance (5)"
eb_chance6$Method="Chance (6)"
eb_chance7$Method="Chance (7)"
eb_chance8$Method="Chance (8)"
eb_chance9$Method="Chance (9)"
eb_chance10$Method="Chance (10)"
eb_sl_45$Method="SL - 45d"
eb_chance1_45$Method="Chance (1) - 45d"
eb_sl_14$Method="SL - 14d"
eb_chance1_14$Method="Chance (1) - 14d"

colnames(eb_sl)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_sl_45)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_sl_14)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_glm)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_NO4T_sl)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_NODEMO_sl)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_NOLAGS_sl)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_NOOTHER_sl)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_NOTIMING_sl)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance1)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance1_45)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance1_14)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance2)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance3)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance4)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance5)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance6)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance7)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance8)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance9)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")
colnames(eb_chance10)<-c("X1","X2","X3","X4","X5","X6","X7","X8","X9","X10","X11","X12","X13","X14","X15","X16","AUC","end","Method")

eb_all<-rbind(eb_sl,eb_glm,eb_NOTIMING_sl,eb_NOLAGS_sl,eb_NODEMO_sl,eb_NO4T_sl,eb_NOOTHER_sl,eb_chance1,eb_chance2,eb_chance3,eb_chance4,eb_chance5,eb_chance6,eb_chance7,eb_chance8,eb_chance9,eb_chance10,eb_sl_45,eb_chance1_45,eb_sl_14,eb_chance1_14)


eb_all$Method<-factor(eb_all$Method, levels=c("SL", "Logistic regression", "SL - without timing", "SL - without lags", "SL - without age/sex", "SL - without 4Ts", "SL - without non-4T flags", "Chance (1)", "Chance (2)", "Chance (3)", "Chance (4)", "Chance (5)", "Chance (6)", "Chance (7)", "Chance (8)", "Chance (9)", "Chance (10)", "SL - 45d", "Chance (1) - 45d", "SL - 14d", "Chance (1) - 14d"), labels=c("SL", "Logistic regression", "SL - without timing", "SL - without lags", "SL - without age/sex", "SL - without 4Ts", "SL - without non-4T flags", "Chance (1)", "Chance (2)", "Chance (3)", "Chance (4)", "Chance (5)", "Chance (6)", "Chance (7)", "Chance (8)", "Chance (9)", "Chance (10)", "SL - 45d", "Chance (1) - 45d", "SL - 14d", "Chance (1) - 14d"))

ltype <- c("SL" = "solid", "Chance (1)" = "dotted", "Chance (2)" = "dotted", "Chance (3)" = "dotted", "Chance (4)" = "dotted", "Chance (5)" = "dotted", "Chance (6)" = "dotted", "Chance (7)" = "dotted", "Chance (8)" = "dotted", "Chance (9)" = "dotted", "Chance (10)" = "dotted", "SL - 45d" = "solid", "Chance (1) - 45d" = "dotted", "SL - 14d" = "solid", "Chance (1) - 14d" = "dotted")

plot_sl<-subset(eb_all,Method=="SL" | Method=="Chance (1)") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="black") +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (1)")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <90 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")

#checking we didn't get lucky with Chance (1)
plot_sl_alt1<-subset(eb_all,Method=="SL" | Method=="Chance (2)") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="black") +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (2)")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <90 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")

plot_sl_alt2<-subset(eb_all,Method=="SL" | Method=="Chance (2)") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="black") +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (2)")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <90 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")

plot_sl_alt3<-subset(eb_all,Method=="SL" | Method=="Chance (3)") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="black") +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (3)")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <90 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")

plot_sl_alt4<-subset(eb_all,Method=="SL" | Method=="Chance (4)") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="black") +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (4)")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <90 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")

plot_sl_alt5<-subset(eb_all,Method=="SL" | Method=="Chance (5)") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="black") +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (5)")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <90 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")



#checking sensitivity to the choice of 90 day window
#First: 45days
plot_sl_45d<-subset(eb_all,Method=="SL - 45d" | Method=="Chance (1) - 45d") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="black") +
  geom_point(aes(x=FourT.effort.45d, y=FourT.benefit.45d), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort.45d, y=ThreeT.benefit.45d), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort.45d, y=TwoT.benefit.45d), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort.45d, y=OneT.benefit.45d), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL - 45d")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (1) - 45d")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort.45d, y=FourT.benefit.45d-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort.45d, y=ThreeT.benefit.45d+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort.45d, y=TwoT.benefit.45d, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort.45d, y=OneT.benefit.45d, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <45 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")


#Second: 14days
plot_sl_14d<-subset(eb_all,Method=="SL - 14d" | Method=="Chance (1) - 14d") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="black") +
  geom_point(aes(x=FourT.effort.14d, y=FourT.benefit.14d), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort.14d, y=ThreeT.benefit.14d), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort.14d, y=TwoT.benefit.14d), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort.14d, y=OneT.benefit.14d), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL - 14d")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (1) - 14d")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort.14d, y=FourT.benefit.14d-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort.14d, y=ThreeT.benefit.14d+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort.14d, y=TwoT.benefit.14d, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort.14d, y=OneT.benefit.14d, label=" Any 1T", hjust=0,
           color="red",size=5) +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <14 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")


plot_sl2<-subset(eb_all,Method=="SL" | Method=="Chance (1)") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  geom_vline(xintercept = .1, color="darkorchid4") +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (1)")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5)  +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <90 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")



plot_sl_vs_glm<-subset(eb_all,Method=="SL" | Method=="Logistic regression" | Method=="Chance (1)") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method,linetype=factor(Method))) + scale_linetype_manual(values=ltype) +
  scale_color_manual(values=c("black", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue", "blue")) +
  #geom_vline(xintercept = .1, color="darkorchid4") +
  geom_point(aes(x=FourT.effort, y=FourT.benefit), colour="red", shape=3) +
  geom_point(aes(x=ThreeT.effort, y=ThreeT.benefit), colour="red", shape=3) +
  geom_point(aes(x=TwoT.effort, y=TwoT.benefit), colour="red", shape=3) +
  geom_point(aes(x=OneT.effort, y=OneT.benefit), colour="red", shape=3) +
  annotate(geom="text", x=0.21, y=0.81, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.41, y=0.65, label=paste("AUC(Chance)=",round(subset(eb_all,Method=="Chance (1)")$AUC[1],3),sep=""), hjust=0,
           color="blue",size=5) +
  annotate(geom="text", x=FourT.effort, y=FourT.benefit-.015, label=" All 4T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=ThreeT.effort, y=ThreeT.benefit+.015, label=" Any 3T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=TwoT.effort, y=TwoT.benefit, label=" Any 2T", hjust=0,
           color="red",size=5) +
  annotate(geom="text", x=OneT.effort, y=OneT.benefit, label=" Any 1T", hjust=0,
           color="red",size=5)  +
  theme_ipsum() +
  theme(legend.position="none",axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=15), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts (children <15yo) with an alert") +
  ylab("Proportion of children with T1D with an alert <90 days from diagnosis") +
  ggtitle("Effort-benefit curve for the SuperLearner algorithm (trained on SAIL, tested on CPRD)")



plot_sl_vs_glm<-subset(eb_all,Method=="SL" | Method=="Logistic regression") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method)) +
  #geom_vline(xintercept = .1, color="black") +
  annotate(geom="text", x=0.25, y=0.75, label=paste("AUC(SL)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.25, y=0.72, label=paste("AUC(LR)=",round(subset(eb_all,Method=="Logistic regression")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate("segment", x = 0, xend = 1, y = 0, yend = subset(eb_all,Method=="SL")$end[1],
           colour = "blue", linetype="dotted") +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts in children <15yo with an alert") +
  ylab("Proportion of children <15yo with T1D who receive an alert up to 90 days before diagnosis") +
  ggtitle("Comparing SuperLearner and Logistic Regression")


plot_comparison_sls<-subset(eb_all,Method!="Logistic regression") %>% ggplot(aes(x=X1,y=X2)) +
  geom_line(aes(colour=Method)) +
  #geom_vline(xintercept = .1, color="black") +
  annotate(geom="text", x=0.25, y=0.72, label=paste("AUC(SL - original)=",round(subset(eb_all,Method=="SL")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.25, y=0.69, label=paste("AUC(SL - without timing)=",round(subset(eb_all,Method=="SL - without timing")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.25, y=0.75, label=paste("AUC(SL - without lags)=",round(subset(eb_all,Method=="SL - without lags")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.25, y=0.66, label=paste("AUC(SL - without age/sex)=",round(subset(eb_all,Method=="SL - without age/sex")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.25, y=0.60, label=paste("AUC(SL - without 4Ts)=",round(subset(eb_all,Method=="SL - without 4Ts")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate(geom="text", x=0.25, y=0.63, label=paste("AUC(SL - without non-4T flags)=",round(subset(eb_all,Method=="SL - without non-4T flags")$AUC[1],3),sep=""), hjust=0,
           color="black",size=5) +
  annotate("segment", x = 0, xend = 1, y = 0, yend = subset(eb_all,Method=="SL")$end[1],
           colour = "blue", linetype="dotted") +
  theme_ipsum() +
  theme(legend.title=element_text(size=14),legend.text=element_text(size=14),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts in children <15yo with an alert") +
  ylab("Proportion of children <15yo with T1D who receive an alert up to 90 days before diagnosis") +
  ggtitle("The performance of the SuperLearner when component features are removed")



plot_sl_mean<-subset(eb_all,Method=="SL") %>% ggplot(aes(x=X1,y=X7)) +
  geom_line(colour="black") +
  #geom_vline(xintercept = .1, color="black") +
  theme_ipsum() +
  theme(legend.text=element_blank(),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts in children <15yo with an alert") +
  ylab("Mean number of days by which diagnosis is anticipated") +
  ggtitle("By how many days (on average) would diagnosis be anticipated?")


plot_sl_75c<-subset(eb_all,Method=="SL") %>% ggplot(aes(x=X1,y=X6)) +
  geom_line(colour="black") +
  #geom_vline(xintercept = .1, color="black") +
  theme_ipsum() +
  theme(legend.text=element_blank(),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts in children <15yo with an alert") +
  ylab("75th centile of the distribution of number of days by which diagnosis is anticipated") +
  ggtitle("At least 25% would have their diagnosis anticipated by at least how many days?")


plot_sl_ppv<-subset(eb_all,Method=="SL") %>% ggplot(aes(x=X1,y=X8)) +
  geom_line(colour="black") +
  #geom_vline(xintercept = .1, color="black") +
  theme_ipsum() +
  theme(legend.text=element_blank(),axis.title.y = element_text(size=14,hjust=0.5), axis.title.x = element_text(size=14,hjust=0.5), plot.title = element_text(size=18), axis.text.x = element_text(size=11), axis.text.y = element_text(size=11), plot.margin = margin(b=0)) +
  xlab("Proportion of GP contacts in children <15yo with an alert") +
  ylab("PPV") +
  ggtitle("Positive predictive value: what is the probability that a child with an alert will have a diagnosis of T1D within 90 days?")



merged_cprd[,n_contacts:=max(EVENT_SEQN),by=new_id2]
merged_cprd[,last_contact:=max(EVENT_DT),by=new_id2]
merged_cprd[,first_contact:=min(EVENT_DT),by=new_id2]
merged_cprd[,length_fup:=last_contact-first_contact]
merged_cprd[,contact_freq:=as.numeric(length_fup)/n_contacts]
quantile(merged_cprd[EVENT_SEQN==1][,length_fup])
quantile(merged_cprd[EVENT_SEQN==1][,contact_freq])

t_fmeans <- merged_cprd[susp_t1d_no_conf_in_diag_date==FALSE][, sapply(.SD, function(x) list(mean = mean(x))), .SDcols = flag_names[1:26]]
sorted_t<-100*t_fmeans[,c(9,19,15,20,26,3,12,6,16,23,5,4,7,10,11,18,24,17,22,8,14,1,2,13,25,21)]
sorted_t<-as.data.frame(t(sorted_t))
sorted_t$Flag=rownames(sorted_t)
sorted_t$Flag<-factor(sorted_t$Flag, levels=c("FAMILY_HISTORY.mean","THIRST.mean","OBESITY.mean","TIREDNESS.mean","POLYURIA.mean","BEHAVIOUR.mean","HEADACHE.mean","BREATHLESSNESS.mean","PREDNISOLONE.mean","VOMITING_NAUSEA.mean","BLURRED_VISION.mean","BLOODS.mean","CONSTIPATION.mean","FUNGAL.mean","GASTROINTESTINAL.mean","SKIN_INFECTIONS.mean","WEIGHT_LOSS.mean","RASH.mean","URINARY.mean","CONTACT_NON_SPEC.mean","NON_ORAL_ABX.mean","ANTIPYRETIC.mean","ATOPICALLERGY.mean","LOWER_RTI.mean","ANTIBIOTICS.mean","UPPER_RTI.mean"), labels=c("FAMILY_HISTORY","THIRST","OBESITY","TIREDNESS","POLYURIA","BEHAVIOUR","HEADACHE","BREATHLESSNESS","PREDNISOLONE","VOMITING_NAUSEA","BLURRED_VISION","BLOODS","CONSTIPATION","FUNGAL","GASTROINTESTINAL","SKIN_INFECTIONS","WEIGHT_LOSS","RASH","URINARY","CONTACT_NON_SPEC","NON_ORAL_ABX","ANTIPYRETIC","ATOPICALLERGY","LOWER_RTI","ANTIBIOTICS","UPPER_RTI"))

means_SAIL<-as.vector(c(0.0002147642,0.00025896,0.0003801245,0.0008208457, 0.00127135, 0.002439836, 0.002458566, 0.002886455, 0.004805348, 0.005024601, 0.005656866, 0.01317692, 0.01615436, 0.01823176, 0.0218467, 0.02244976, 0.02385289, 0.02518754, 0.02557414, 0.03156349, 0.03181071, 0.07956466, 0.09075237, 0.1105915, 0.1128688, 0.1162691))

fmeans_compare<-sorted_t
rownames(fmeans_compare)<-1:26
colnames(fmeans_compare)<-c("Percentage_CPRD","Flag")

SAIL_df<-as.data.frame(100*means_SAIL)
colnames(SAIL_df)<-c("Percentage_SAIL")


fmeans_compare=cbind(fmeans_compare,SAIL_df)

library(grid)
g.mid<-ggplot(fmeans_compare,aes(x=1,y=Flag))+geom_text(aes(label=Flag))+
  geom_segment(aes(x=0.94,xend=0.96,yend=Flag))+
  geom_segment(aes(x=1.04,xend=1.065,yend=Flag))+
  ggtitle("")+
  ylab(NULL)+
  scale_x_continuous(expand=c(0,0),limits=c(0.94,1.065))+
  theme(axis.title=element_blank(),
        panel.grid=element_blank(),
        axis.text.y=element_blank(),
        axis.ticks.y=element_blank(),
        panel.background=element_blank(),
        axis.text.x=element_text(color=NA),
        axis.ticks.x=element_line(color=NA),
        plot.margin = unit(c(1,-1,6,-1), "mm"))

flag_plot1 <- ggplot(data = fmeans_compare, aes(x=Flag, y=Percentage_SAIL)) +
  geom_bar(stat = "identity") + ggtitle("Development (SAIL)") + ylim(13,0) + 
  geom_text(aes(label = signif(Percentage_SAIL,c(1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3)), vjust = .5, hjust=1.5)) +
  theme(axis.title.y = element_blank(), 
        axis.text.y = element_blank(), 
        axis.ticks.y = element_blank(), 
        plot.margin = unit(c(1,-1,1,0), "mm")) + ylab("Percentage") + coord_flip()

flag_plot2 <- ggplot(data = fmeans_compare, aes(x=Flag, y=Percentage_CPRD)) +
  geom_bar(stat = "identity") + ggtitle("Validation (CPRD/HES)") + ylim(0,13) + 
  geom_text(aes(label = signif(Percentage_CPRD,c(1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3)), vjust = .5, hjust=-0.5)) +
  theme(axis.title.y = element_blank(), 
        axis.text.y = element_blank(), 
        axis.ticks.y = element_blank(), 
        plot.margin = unit(c(1,0,1,-1), "mm")) + ylab("Percentage") +
  coord_flip()

library(gridExtra)
flag_gg1 <- ggplot_gtable(ggplot_build(flag_plot1))
flag_gg2 <- ggplot_gtable(ggplot_build(flag_plot2))
flag_gg.mid <- ggplot_gtable(ggplot_build(g.mid))

flag_compare_plot<-grid.arrange(flag_gg1,flag_gg.mid,flag_gg2,ncol=3,widths=c(.42,.16,.42))


#which are the consultations that would be flagged by the algorithm at the "10% of consultations" threshold?
merged_cprd[,flag_10:=SLp>=0.027]
merged_cprd[,flag_4p6:=SLp>=0.2245]


#THRESHOLD = 7 days
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 7 DAYS* that would be flagged by the algorithm at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch:=(SLp>=0.027 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=7)]

#who are the T1Ds who would be spotted by this definition (flag within 7 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch_sometime:=max(flag_10_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 7 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_10_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_10_catch_sometime==1,ifelse(SLp>=0.027 &  time_until_diagnosis<=7,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_10_max_days_ant:=max(flag_10_days_ant),by=new_id2]

mean(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][flag_10_catch_sometime==1][,flag_10_max_days_ant])


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_max_days_ant])



#THRESHOLD = 7 days and 4.6% of all contacts alerted
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 7 DAYS* that would be flagged by the algorithm at the "4.6% of consultations" threshold?
merged_cprd[,flag_4p6_catch:=(SLp>=0.2245 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=7)]

#who are the T1Ds who would be spotted by this definition (flag within 7 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_4p6_catch_sometime:=max(flag_4p6_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 7 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_4p6_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_4p6_catch_sometime==1,ifelse(SLp>=0.2245 &  time_until_diagnosis<=7,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_4p6_max_days_ant:=max(flag_4p6_days_ant),by=new_id2]


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_4p6_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_4p6_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_4p6_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_4p6_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_4p6_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_4p6_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_4p6_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_4p6_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_4p6_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_4p6_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_4p6_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_4p6_max_days_ant])

sum(merged_cprd[,(THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)==4])/43108456
sum(merged_cprd[,(THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=3])/43108456
sum(merged_cprd[,(THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=2])/43108456
sum(merged_cprd[,(THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=1])/43108456

#Compare with ALL of the 4 Ts
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 7 DAYS* that would be flagged by the "All 4 Ts" threshold?
merged_cprd[,flag_All4T_catch:=((THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)==4 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=7)]

#who are the T1Ds who would be spotted by this definition (flag within 7 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_All4T_catch_sometime:=max(flag_All4T_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 7 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_All4T_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_All4T_catch_sometime==1,ifelse((THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)==4 &  time_until_diagnosis<=7,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_All4T_max_days_ant:=max(flag_All4T_days_ant),by=new_id2]


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_All4T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_All4T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_All4T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_All4T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_All4T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_All4T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_All4T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_All4T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_All4T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_All4T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_All4T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_All4T_max_days_ant])





#Compare with ANY 3 of the Ts
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 7 DAYS* that would be flagged by the "Any 3 of the Ts" threshold?
merged_cprd[,flag_Any3T_catch:=((THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=3 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=7)]

#who are the T1Ds who would be spotted by this definition (flag within 7 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_Any3T_catch_sometime:=max(flag_Any3T_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 7 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_Any3T_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_Any3T_catch_sometime==1,ifelse((THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=3 &  time_until_diagnosis<=7,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_Any3T_max_days_ant:=max(flag_Any3T_days_ant),by=new_id2]


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_Any3T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_Any3T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_Any3T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_Any3T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_Any3T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_Any3T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_Any3T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_Any3T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_Any3T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_Any3T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_Any3T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_Any3T_max_days_ant])




#Compare with ANY 2 of the Ts
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 7 DAYS* that would be flagged by the "Any 2 of the Ts" threshold?
merged_cprd[,flag_Any2T_catch:=((THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=2 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=7)]

#who are the T1Ds who would be spotted by this definition (flag within 7 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_Any2T_catch_sometime:=max(flag_Any2T_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 7 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_Any2T_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_Any2T_catch_sometime==1,ifelse((THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=2 &  time_until_diagnosis<=7,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_Any2T_max_days_ant:=max(flag_Any2T_days_ant),by=new_id2]


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_Any2T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_Any2T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_Any2T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_Any2T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_Any2T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_Any2T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_Any2T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_Any2T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_Any2T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_Any2T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_Any2T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_Any2T_max_days_ant])




#Compare with ANY 1 of the Ts
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 7 DAYS* that would be flagged by the "Any 1 of the Ts" threshold?
merged_cprd[,flag_Any1T_catch:=((THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=1 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=7)]

#who are the T1Ds who would be spotted by this definition (flag within 7 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_Any1T_catch_sometime:=max(flag_Any1T_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 7 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_Any1T_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_Any1T_catch_sometime==1,ifelse((THIRST+TIREDNESS+WEIGHT_LOSS+POLYURIA)>=1 &  time_until_diagnosis<=7,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_Any1T_max_days_ant:=max(flag_Any1T_days_ant),by=new_id2]


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_Any1T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_Any1T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_Any1T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_Any1T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_Any1T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_Any1T_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_Any1T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_Any1T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_Any1T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_Any1T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_Any1T_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_Any1T_max_days_ant])

#THRESHOLD = 14 days
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 14 DAYS* that would be flagged by the algorithm at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch:=(SLp>=0.027 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=14)]

#who are the T1Ds who would be spotted by this definition (flag within 14 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch_sometime:=max(flag_10_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 14 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_10_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_10_catch_sometime==1,ifelse(SLp>=0.027 &  time_until_diagnosis<=14,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_10_max_days_ant:=max(flag_10_days_ant),by=new_id2]


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_max_days_ant])

#THRESHOLD = 30 days
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 30 DAYS* that would be flagged by the algorithm at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch:=(SLp>=0.027 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=30)]

#who are the T1Ds who would be spotted by this definition (flag within 30 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch_sometime:=max(flag_10_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 30 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_10_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_10_catch_sometime==1,ifelse(SLp>=0.027 &  time_until_diagnosis<=30,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_10_max_days_ant:=max(flag_10_days_ant),by=new_id2]


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_max_days_ant])


#THRESHOLD = 42 days
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 42 DAYS* that would be flagged by the algorithm at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch:=(SLp>=0.027 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=42)]

#who are the T1Ds who would be spotted by this definition (flag within 42 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch_sometime:=max(flag_10_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 42 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_10_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_10_catch_sometime==1,ifelse(SLp>=0.027 &  time_until_diagnosis<=42,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_10_max_days_ant:=max(flag_10_days_ant),by=new_id2]


table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_max_days_ant])


#THRESHOLD = 90 days
#which are the consultations *IN THOSE WHO WILL BE DIAGNOSED WITHIN 90 DAYS* that would be flagged by the algorithm at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch:=(SLp>=0.027 & is.na(t1d_diag_dt)==FALSE & time_until_diagnosis<=90)]

#who are the T1Ds who would be spotted by this definition (flag within 42 days of diagnosis) at the "10% of consultations" threshold?
merged_cprd[,flag_10_catch_sometime:=max(flag_10_catch),by=new_id2]

#when a flag is raised in a patient who will be T1D within 42 days, how many days prior to diagnosis is this consultation?
merged_cprd[,flag_10_days_ant:=ifelse(is.na(t1d_diag_dt)==FALSE & flag_10_catch_sometime==1,ifelse(SLp>=0.027 &  time_until_diagnosis<=90,time_until_diagnosis,0),NA)]

#what is the maximum number of days by which diagnosis is anticipated for each patient?
merged_cprd[,flag_10_max_days_ant:=max(flag_10_days_ant),by=new_id2]

mean(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][flag_10_catch_sometime==1][,flag_10_max_days_ant])

table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_catch_sometime])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==0][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][diagnosis_in_DKA==1][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_u5==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_5t11==TRUE][,flag_10_max_days_ant])
table(merged_cprd[EVENT_SEQN==1][is.na(t1d_diag_dt)==FALSE][AGE_AT_T1D_DIAG_11p==TRUE][,flag_10_max_days_ant])

```

```{r the-end}

```
